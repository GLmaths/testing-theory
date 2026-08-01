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

(** * Completeness of the [ax_pre] proof system w.r.t. [⊑ₘᵤₛₜᵢ]

    The converse of [SoundnessAx.v], for the [Static] fragment. The
    plan, and the material it rests on:

    - [full_normalize] ([VCCS_NormalForm.v]) puts both sides into
      [tau_nf] shape — an internal choice of *stable* guarded sums,
      Hennessy's [⊕ᵢ Σ_{a ∈ Aᵢ} a.p(a)].
    - [coR_abs_incl_iff] ([VCCS_ReadySet.v]) turns [≼ₐₛ]'s abstracted
      ready-set inclusion, for two stable sums, into a plain structural
      fact about which channels they offer.
    - The derivation is then assembled from [ax_int_l]/[_r] and
      [ax_int_glb] on the [⊕] layer, [ax_choice_stable] +
      [ax_input]/[ax_output] on the stable layer, and the two closure
      laws for acceptance families: union closure ([ax_int_below_ext],
      derived, [VCCS_Canonical.v]) and convex closure ([ax_convex],
      primitive, [DefinitionAxiomatic.v]).

    This file currently holds the trace-shift step, which is what lets
    the construction recurse into continuations. *)

From Stdlib Require Import List Permutation PeanoNat Lia.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base sets gmap.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization
  VCCS_Expansion VCCS_ResNormalize VCCS_Precongruence VCCS_ReadySet
  DefinitionAxiomatic VCCS_Canonical VCCS_NormalForm SoundnessAx.

Section CompletenessAx.

Context `{VP : VCCS_Parameters}.

(** ** Shifting the preorder past one visible action

    The completeness construction matches two normal forms summand by
    summand and then has to recurse into the matched continuations. To
    do that it needs [p ⊑ₘᵤₛₜᵢ q] to yield a corresponding relation
    between "[p] after [a]" and "[q] after [a]".

    Neither "after" is a single reduct in general: [p]'s [tau_nf] tree
    may offer [a] from several leaves, so its [a]-behaviour is realised
    by the *internal choice* of those leaves' continuations. Rather
    than commit to a construction, the lemma is stated against whatever
    [pa] and [qa] realise the shifted behaviour — and only on **stable**
    targets, which is exactly what [bhv_pre_cond2] quantifies over.
    That weakening matters: an internal choice of continuations reaches
    itself in zero steps, and that state is not a reduct of [p] after
    [a] at all, but it is not stable either, so it never has to be.

    The [q]-side needs only one direction (every stable state [qa]
    reaches is one [q] reaches after [a]); the [p]-side needs the [iff],
    since the witness comes back from [p] and has to be replayed on
    [pa]. [cond1] is free: [Static] processes converge on every trace
    ([Static_converge], [VCCS_Static.v]). *)

Lemma bhv_pre_shift : forall (p q pa qa : proc) (a : ExtAct TypeOfActions),
  Static p -> Static qa ->
  (forall s r, r ↛ -> (pa ⟹[s] r <-> p ⟹[a :: s] r)) ->
  (forall s r, r ↛ -> (qa ⟹[s] r -> q ⟹[a :: s] r)) ->
  p ≼ₐₛ q -> pa ≼ₐₛ qa.
Proof.
  intros p q pa qa a Hp Hqa Hpiff Hqimp (Hc1 & Hc2).
  split.
  - intros s _. apply Static_converge. exact Hqa.
  - intros s qa' _ Hwt Hst.
    destruct (Hc2 (a :: s) qa' (Static_converge (a :: s) p Hp) (Hqimp s qa' Hst Hwt) Hst)
      as (p' & Hwp & Hstp & Hincl).
    exists p'. repeat split; [| exact Hstp | exact Hincl].
    apply Hpiff; assumption.
Qed.

Corollary must_i_shift : forall (p q pa qa : proc) (a : ExtAct TypeOfActions),
  Static p -> Static qa ->
  (forall s r, r ↛ -> (pa ⟹[s] r <-> p ⟹[a :: s] r)) ->
  (forall s r, r ↛ -> (qa ⟹[s] r -> q ⟹[a :: s] r)) ->
  p ⊑ₘᵤₛₜᵢ q -> pa ⊑ₘᵤₛₜᵢ qa.
Proof.
  intros p q pa qa a Hp Hqa Hpiff Hqimp Hpre.
  apply must_iff_acceptance_set_VCCS_without_toFW.
  apply bhv_pre_shift with (p := p) (q := q) (a := a);
    [exact Hp | exact Hqa | exact Hpiff | exact Hqimp |].
  apply must_iff_acceptance_set_VCCS_without_toFW. exact Hpre.
Qed.

(** ** The leaves of a normal form

    A [tau_nf] process is a binary tree of internal choices whose leaves
    are [gStable] guarded sums. [leaves] reads that list of leaves off
    the syntax, and [leafsum] is their *external* sum — the two objects
    the matching argument compares against a stable right-hand side.

    [leaves] is written with the boolean test [gStableB] in front rather
    than by recursion on a [tau_nf] derivation, so that it is an ordinary
    [Fixpoint] usable inside other definitions; the [𝛕]-branches sit two
    constructors deep, which the guard checker accepts (same shape as
    [tau_nfB], [VCCS_Canonical.v]). Since it inspects [gStableB M] before
    [M]'s own constructor, [simpl] cannot unfold it at a variable —
    [leaves_eq] is the rewriting equation to use instead, and every
    proof below leads with it. *)

Fixpoint leaves (M : gproc) : list gproc :=
  if gStableB M then [M]
  else match M with
       | (𝛕 • (g A)) + (𝛕 • (g B)) => leaves A ++ leaves B
       | _ => [M]
       end.

Lemma leaves_eq : forall M, leaves M =
  if gStableB M then [M]
  else match M with
       | (𝛕 • (g A)) + (𝛕 • (g B)) => leaves A ++ leaves B
       | _ => [M]
       end.
Proof. intro M. destruct M; reflexivity. Qed.

Lemma leaves_gStatic : forall M, gStatic M -> Forall gStatic (leaves M).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intro HM. rewrite leaves_eq.
  destruct (gStableB M) eqn:E; [constructor; [exact HM | constructor] |].
  destruct M; try (constructor; [exact HM | constructor]).
  destruct M1; try (constructor; [exact HM | constructor]).
  destruct p; try (constructor; [exact HM | constructor]).
  destruct M2; try (constructor; [exact HM | constructor]).
  destruct p; try (constructor; [exact HM | constructor]).
  inversion HM; subst. inversion H1; subst. inversion H2; subst.
  inversion H0; subst. inversion H3; subst.
  apply Forall_app. split.
  - apply IH; [simpl; lia | assumption].
  - apply IH; [simpl; lia | assumption].
Qed.

Lemma leaves_stable : forall M, tau_nf M -> Forall gStable (leaves M).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intro HM. rewrite leaves_eq.
  destruct (gStableB M) eqn:E.
  - constructor; [apply gStableB_spec; exact E | constructor].
  - inversion HM as [? Hs | A B HA HB]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + simpl. apply Forall_app. split.
      * apply IH; [simpl; lia | exact HA].
      * apply IH; [simpl; lia | exact HB].
Qed.

(** Every leaf is derivably *above* the whole normal form — one
    [ax_int_l]/[ax_int_r] per level of the [⊕]-tree. This is how the
    matching argument discards the leaves it does not need. *)

Lemma leaves_below : forall M, tau_nf M ->
  forall A, A ∈ leaves M -> ax_pre (g M) (g A).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HM A Hin. rewrite leaves_eq in Hin.
  destruct (gStableB M) eqn:E.
  - assert (A = M) by set_solver. subst. apply ax_refl.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + simpl in Hin. apply elem_of_app in Hin. destruct Hin as [Hin | Hin].
      * eapply ax_trans; [apply ax_int_l | apply IH; [simpl; lia | exact H1 | exact Hin]].
      * eapply ax_trans; [apply ax_int_r | apply IH; [simpl; lia | exact H2 | exact Hin]].
Qed.

Definition leafsum (M : gproc) : gproc := rebuild (leaves M).

Lemma leafsum_gStatic : forall M, gStatic M -> gStatic (leafsum M).
Proof. intros M HM. apply rebuild_gStatic. apply leaves_gStatic. exact HM. Qed.

(** The external sum of all leaves is derivably above the normal form
    too — this is union closure of the acceptance family, and it is
    where [ax_int_below_ext] ([VCCS_Canonical.v]) earns its keep. The
    [⊕]-congruence step needs [ax_choice_tau] *twice*, with a
    commutation in between, because the rule only ever rewrites the
    leftmost summand. *)

Lemma ax_leafsum : forall M, gStatic M -> tau_nf M -> ax_pre (g M) (g (leafsum M)).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HMst HM. unfold leafsum. rewrite leaves_eq.
  destruct (gStableB M) eqn:E.
  - simpl. apply ax_cgr; [constructor; constructor; [exact HMst | constructor] |].
    apply cgr_choice_nil_rev.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + inversion HMst; subst.
      inversion H3; subst. inversion H4; subst.
      inversion H0; subst. inversion H5; subst.
      assert (Hl1 : ax_pre (g M1) (g (leafsum M1)))
        by (apply IH; [simpl; lia | exact H6 | exact H1]).
      assert (Hl2 : ax_pre (g M2) (g (leafsum M2)))
        by (apply IH; [simpl; lia | exact H7 | exact H2]).
      eapply ax_trans; [apply (ax_choice_tau (g M1) (g (leafsum M1)) (𝛕 • (g M2))); exact Hl1 |].
      eapply ax_trans;
        [apply ax_cgr with (q := g ((𝛕 • (g M2)) + (𝛕 • (g (leafsum M1)))));
           [repeat constructor; [exact H7 | apply leafsum_gStatic; exact H6]
           | apply cgr_choice_com] |].
      eapply ax_trans;
        [apply (ax_choice_tau (g M2) (g (leafsum M2)) (𝛕 • (g (leafsum M1)))); exact Hl2 |].
      eapply ax_trans;
        [apply ax_int_below_ext; apply leafsum_gStatic; [exact H7 | exact H6] |].
      apply ax_cgr.
      * apply static_g. apply rebuild_gStatic. apply Forall_app.
        split; apply leaves_gStatic; assumption.
      * transitivity (g (leafsum M1 + leafsum M2)); [apply cgr_choice_com |].
        symmetry. apply rebuild_app.
Qed.

(** The converse reading of [leaves]: the *stable* states a normal form
    reaches by internal moves alone are exactly its leaves. This is what
    turns [bhv_pre_cond2]'s witness at the empty trace — an anonymous
    stable reduct — into a concrete leaf the derivation can name. *)

Lemma leaves_wt_stable : forall M, tau_nf M -> forall r, (g M) ⟹[[]] r -> r ↛ ->
  exists A, A ∈ leaves M /\ r = g A.
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HM r Hwt Hst.
  inversion HM as [? Hs | M1 M2 H1 H2]; subst.
  - exists M. split; [rewrite leaves_eq; rewrite (proj2 (gStableB_spec M) Hs); set_solver |].
    apply (wt_nil_stable (g M) r); [apply gStable_iff; exact Hs | exact Hwt].
  - assert (E : gStableB ((𝛕 • (g M1)) + (𝛕 • (g M2))) = false) by reflexivity.
    rewrite leaves_eq. rewrite E.
    inversion Hwt; subst.
    + exfalso.
      assert (Hl : lts (g ((𝛕 • (g M1)) + (𝛕 • (g M2)))) τ (g M1))
        by (apply lts_choiceL; apply lts_tau).
      pose proof (lts_set_spec1 _ _ _ Hl) as Hmem.
      rewrite Hst in Hmem. set_solver.
    + inversion l; subst.
      * inversion H5; subst.
        destruct (IH M1 ltac:(simpl; lia) H1 r w Hst) as (A & Hin & Heq).
        exists A. split; [apply elem_of_app; left; exact Hin | exact Heq].
      * inversion H5; subst.
        destruct (IH M2 ltac:(simpl; lia) H2 r w Hst) as (A & Hin & Heq).
        exists A. split; [apply elem_of_app; right; exact Hin | exact Heq].
Qed.

(** ** The convexity step, at an arbitrary summand split

    [ax_convex]'s literal shape demands the middle term be syntactically
    [(X + Y) + Z] with the same [X] as the first branch. In practice all
    that is known is a *permutation* of summands, so this is the usable
    form — the analogue of [ax_collapse_*_anywhere] and
    [ax_tau_sep_anywhere] ([VCCS_Canonical.v]) for the convexity rule.

    Unlike those, no [𝟘]-padding mismatch arises: [rebuild_app] absorbs
    each [rebuild]'s trailing [𝟘] on both sides of the equation, so the
    two summand lists never have to be compared up to units. And the
    rewrite goes through [ax_cgr] on the *whole* term rather than
    [ax_choice_tau], since [≡*] is a full congruence — [cgr_fullchoice]
    plus [cgr_tau] reach inside the second [𝛕]-branch directly. *)

Lemma summands_rebuild_perm : forall l l', Permutation l l' ->
  Permutation (summands (rebuild l)) (summands (rebuild l')).
Proof.
  intros l l' Hp. induction Hp; simpl.
  - reflexivity.
  - apply Permutation_app_head. exact IHHp.
  - repeat rewrite app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - etransitivity; eassumption.
Qed.

(** A hand-rolled boolean partition. stdpp's [filter] is typeclass-based
    and does not reduce under [simpl] here, and both halves' properties
    are wanted anyway, so a plain [Fixpoint] is less friction. *)

Fixpoint split_by (f : gproc -> bool) (l : list gproc) : list gproc * list gproc :=
match l with
| [] => ([], [])
| a :: l' =>
    match split_by f l' with
    | (y, z) => if f a then (a :: y, z) else (y, a :: z)
    end
end.

Lemma split_by_perm : forall f l,
  Permutation l ((split_by f l).1 ++ (split_by f l).2).
Proof.
  intros f l. induction l as [|a l IH]; simpl; [reflexivity |].
  destruct (split_by f l) as (y, z). simpl in IH.
  destruct (f a); simpl.
  - apply perm_skip. exact IH.
  - etransitivity; [apply perm_skip; exact IH | apply Permutation_middle].
Qed.

Lemma split_by_fst : forall f l, Forall (fun a => f a = true) (split_by f l).1.
Proof.
  intros f l. induction l as [|a l IH]; simpl; [constructor |].
  destruct (split_by f l) as (y, z). simpl in IH.
  destruct (f a) eqn:E; simpl; [constructor; assumption | exact IH].
Qed.

Lemma split_by_snd : forall f l, Forall (fun a => f a = false) (split_by f l).2.
Proof.
  intros f l. induction l as [|a l IH]; simpl; [constructor |].
  destruct (split_by f l) as (y, z). simpl in IH.
  destruct (f a) eqn:E; simpl; [exact IH | constructor; assumption].
Qed.

Lemma split_by_incl : forall f l a, a ∈ (split_by f l).1 -> a ∈ l.
Proof.
  intros f l a Hin. rewrite (split_by_perm f l). apply elem_of_app. left. exact Hin.
Qed.

Theorem ax_convex_anywhere : forall W A Y Z,
  gStatic A -> Forall gStatic Y -> Forall gStatic Z ->
  Permutation (summands W) (summands A ++ (Y ++ Z)) ->
  ax_pre (g ((𝛕 • (g A)) + (𝛕 • (g W)))) (g (A + rebuild Y)).
Proof.
  intros W A Y Z HA HY HZ Hperm.
  assert (HrY : gStatic (rebuild Y)) by (apply rebuild_gStatic; exact HY).
  assert (HrZ : gStatic (rebuild Z)) by (apply rebuild_gStatic; exact HZ).
  assert (Hcgr : g W ≡* g ((A + rebuild Y) + rebuild Z)).
  { transitivity (g (rebuild (summands W))); [apply summands_cgr |].
    transitivity (g (rebuild (summands A ++ (Y ++ Z)))); [apply rebuild_perm; exact Hperm |].
    transitivity (g (rebuild (summands A) + rebuild (Y ++ Z))); [apply rebuild_app |].
    transitivity (g (A + rebuild (Y ++ Z))).
    - apply cgr_choice. symmetry. apply summands_cgr.
    - transitivity (g (A + (rebuild Y + rebuild Z))).
      + apply cgr_fullchoice; [reflexivity | apply rebuild_app].
      + apply cgr_choice_assoc_rev. }
  eapply ax_trans;
    [apply ax_cgr with (q := g ((𝛕 • (g A)) + (𝛕 • (g ((A + rebuild Y) + rebuild Z)))))
    | apply ax_convex].
  - repeat constructor; [exact HA | exact HA | exact HrY | exact HrZ].
  - apply cgr_fullchoice; [reflexivity | apply cgr_tau; exact Hcgr].
Qed.

(** The glue: a leaf's own summands sit inside [leafsum M]'s, with a
    definite remainder — exactly the [Permutation] hypothesis
    [ax_convex_anywhere] consumes, once the remainder is split by
    [split_by] on "is this action offered by the right-hand side?". *)

Lemma leafsum_split : forall M A, gStatic M -> A ∈ leaves M ->
  exists R, Permutation (summands (leafsum M)) (summands A ++ R) /\ Forall gStatic R.
Proof.
  intros M A HM Hin.
  apply elem_of_Permutation in Hin. destruct Hin as (k & Hp).
  assert (Hst : Forall gStatic (A :: k)).
  { eapply Permutation_Forall; [exact Hp | apply leaves_gStatic; exact HM]. }
  inversion Hst as [|? ? _ Hk]; subst.
  exists (summands (rebuild k)). split.
  - unfold leafsum. etransitivity; [apply summands_rebuild_perm; exact Hp | reflexivity].
  - apply summands_gStatic. apply rebuild_gStatic. exact Hk.
Qed.

(** ** Matching two stable sums summand by summand

    Given a pairing of the two sums' summands with [⊢]-related members,
    the sums themselves are [⊢]-related.

    An earlier reading of the system said list-structural recursion over
    summands was impossible, because rewriting the *tail* of [w :: l]
    while the head stays put is congruence in the second argument of
    [+], which the system deliberately lacks (it is the unsound
    [ax_choice]). That is right as stated but not an obstacle: commute
    first. [ax_choice_stable] rewrites the *leftmost* summand in an
    arbitrary context, so putting the recursion's own subject there —
    [rebuild lw + n] rather than [n + rebuild lw] — makes the step go
    through. Each cons therefore costs two [ax_choice_stable]s and two
    commutations: one to replace the head, one to replace the tail.

    Both sums must be stable throughout, which is exactly
    [ax_choice_stable]'s side condition and is what
    [gStable_rebuild] maintains along the recursion. *)

Lemma gStable_rebuild : forall l, Forall gStable l -> gStable (rebuild l).
Proof.
  induction l as [|a l IH]; intro H; simpl; [exact I |].
  inversion H; subst. split; [assumption | apply IH; assumption].
Qed.

Lemma ax_match_lists : forall lw ln,
  Forall gStatic lw -> Forall gStatic ln ->
  Forall gStable lw -> Forall gStable ln ->
  Forall2 (fun w n => ax_pre (g w) (g n)) lw ln ->
  ax_pre (g (rebuild lw)) (g (rebuild ln)).
Proof.
  intros lw ln Hsw Hsn Hbw Hbn H2.
  induction H2 as [| w n lw ln Hwn H2 IH]; simpl; [apply ax_refl |].
  inversion Hsw as [|? ? Hw Hsw']; subst.
  inversion Hsn as [|? ? Hn Hsn']; subst.
  inversion Hbw as [|? ? Hbw0 Hbw']; subst.
  inversion Hbn as [|? ? Hbn0 Hbn']; subst.
  assert (Hrw : gStatic (rebuild lw)) by (apply rebuild_gStatic; exact Hsw').
  assert (Hrn : gStatic (rebuild ln)) by (apply rebuild_gStatic; exact Hsn').
  eapply ax_trans; [apply (ax_choice_stable w n (rebuild lw)); assumption |].
  eapply ax_trans;
    [apply ax_cgr with (q := g (rebuild lw + n));
       [constructor; constructor; assumption | apply cgr_choice_com] |].
  eapply ax_trans;
    [apply (ax_choice_stable (rebuild lw) (rebuild ln) n);
       [apply gStable_rebuild; exact Hbw' | apply gStable_rebuild; exact Hbn'
        | apply IH; assumption] |].
  apply ax_cgr with (q := g (n + rebuild ln));
    [constructor; constructor; assumption | apply cgr_choice_com].
Qed.

(** ** Internal choice over a list

    The realiser [must_i_shift] was stated against: "[M] after [a]" is
    not any single leaf's continuation but the internal choice of *all*
    of them. With [M = a•p ⊕ (a•q + b•r)], what [M ⊑ₘᵤₛₜᵢ N] constrains
    is [p ⊕ q] against [n_a] — it says nothing about [p] alone.

    Two design points:
    - The singleton case is [(𝛕 • p) + (𝛕 • p)] rather than the obvious
      [𝛕 • p], so that [ax_int_l]/[ax_int_glb] apply directly. The
      obvious version would need [⊢ g (𝛕 • p) ≂ p] (Milner's first
      [𝛕]-law), which is *not* evidently derivable here — no rule has a
      lone [𝛕]-guard on either side. Duplicating sidesteps the question;
      it does not arise from [full_normalize] either, whose [⊕]-nodes are
      always binary.
    - The empty case is [𝟘], which is wrong as an internal choice, so
      every lemma below that needs it takes the list as [p0 :: l].

    [ax_ichoice_below] and [ax_ichoice_glb] are the n-ary [ax_int_l] and
    [ax_int_glb]. Both go through [ax_tau_flatten], whose [gAllTau] side
    condition is exactly what an [ichoice] tail satisfies — the concrete
    reason this shape (rather than [rebuild] over [𝛕]-guards) was
    chosen: [rebuild]'s trailing [𝟘] would break [gAllTau]. *)

Fixpoint ichoice (l : list proc) : gproc :=
match l with
| [] => 𝟘
| [p] => (𝛕 • p) + (𝛕 • p)
| p :: l' => (𝛕 • p) + ichoice l'
end.

Lemma ichoice_gStatic : forall l, Forall Static l -> gStatic (ichoice l).
Proof.
  induction l as [|p l IH]; intro H; simpl; [constructor |].
  inversion H as [|? ? Hp Hl]; subst.
  destruct l as [|p2 l2]; [repeat constructor; exact Hp |].
  constructor; [constructor; exact Hp | apply IH; exact Hl].
Qed.

Lemma ichoice_gAllTau : forall p l, gAllTau (ichoice (p :: l)).
Proof.
  intros p l. revert p. induction l as [|p2 l2 IH]; intro p; simpl.
  - split; exact I.
  - split; [exact I |]. apply (IH p2).
Qed.

Lemma ax_ichoice_below : forall l p, Forall Static l -> p ∈ l ->
  ax_pre (g (ichoice l)) p.
Proof.
  induction l as [|p0 l IH]; intros p Hst Hin; [set_solver |].
  inversion Hst as [|? ? Hp0 Hl]; subst.
  destruct l as [|p1 l1].
  - assert (p = p0) by set_solver. subst. simpl. apply ax_int_l.
  - eapply ax_trans;
      [apply (ax_tau_flatten_r (𝛕 • p0) (ichoice (p1 :: l1))); apply ichoice_gAllTau |].
    apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + subst. apply ax_int_l.
    + eapply ax_trans; [apply ax_int_r | apply IH; assumption].
Qed.

Lemma ax_ichoice_glb : forall l q, l <> [] -> Forall Static l ->
  (forall p, p ∈ l -> ax_pre q p) -> ax_pre q (g (ichoice l)).
Proof.
  induction l as [|p0 l IH]; intros q Hne Hst Hall; [contradiction |].
  inversion Hst as [|? ? Hp0 Hl]; subst.
  destruct l as [|p1 l1].
  - simpl. apply ax_int_glb; apply Hall; set_solver.
  - eapply ax_trans;
      [| apply (ax_tau_flatten_l (𝛕 • p0) (ichoice (p1 :: l1))); apply ichoice_gAllTau].
    apply ax_int_glb.
    + apply Hall. set_solver.
    + apply IH; [discriminate | exact Hl |].
      intros p Hin. apply Hall. apply elem_of_cons. right. exact Hin.
Qed.

(** The reachability side: an [ichoice] must commit through one of its
    [𝛕]s before doing anything, so its stable reducts are exactly the
    union of its members'. This is the [pa]-side hypothesis of
    [must_i_shift] — and the reason that hypothesis was restricted to
    stable targets: [g (ichoice l)] reaches *itself* in zero steps, and
    that state is a reduct of no member at all, but it is not stable
    either. *)

Lemma ichoice_lts_tau : forall l q, lts (g (ichoice l)) τ q <-> q ∈ l.
Proof.
  induction l as [|p0 l IH]; intro q; split; intro H.
  - simpl in H. inversion H.
  - set_solver.
  - destruct l as [|p1 l1].
    + simpl in H. inversion H; subst; inversion H4; subst; set_solver.
    + simpl in H. inversion H; subst.
      * inversion H4; subst. set_solver.
      * apply elem_of_cons. right. apply IH. exact H4.
  - destruct l as [|p1 l1].
    + assert (q = p0) by set_solver. subst. simpl. apply lts_choiceL. apply lts_tau.
    + apply elem_of_cons in H. destruct H as [Heq | Hin].
      * subst. simpl. apply lts_choiceL. apply lts_tau.
      * simpl. apply lts_choiceR. apply IH. exact Hin.
Qed.

Lemma ichoice_wt_stable : forall p0 l r s, r ↛ ->
  ((g (ichoice (p0 :: l))) ⟹[s] r <-> exists p, p ∈ (p0 :: l) /\ p ⟹[s] r).
Proof.
  intros p0 l r s Hst. split.
  - intro Hwt. inversion Hwt; subst.
    + exfalso.
      assert (Hl : lts (g (ichoice (p0 :: l))) τ p0) by (apply ichoice_lts_tau; set_solver).
      pose proof (lts_set_spec1 _ _ _ Hl) as Hmem. rewrite Hst in Hmem. set_solver.
    + exists q. split; [apply ichoice_lts_tau; exact l0 | exact w].
    + exfalso. eapply gAllTau_no_ext; [apply ichoice_gAllTau | exact l0].
  - intros (p & Hin & Hwp).
    eapply wt_tau; [apply ichoice_lts_tau; exact Hin | exact Hwp].
Qed.

(** ** Factoring a normal form's weak transitions through its leaves

    A [tau_nf] does its internal moves *first*, reaching a leaf, and only
    then a visible action: its [⊕]-nodes have no external transitions at
    all. [leaves_reach] is the forward half (every leaf is [τ]-reachable)
    and [leaves_wt_cons] the backward one. Together with
    [leaves_wt_stable] above they pin down [⟹] on a normal form
    completely. *)

Lemma leaves_reach : forall M, tau_nf M ->
  forall A, A ∈ leaves M -> (g M) ⟹[[]] (g A).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HM A Hin. rewrite leaves_eq in Hin.
  destruct (gStableB M) eqn:E.
  - assert (A = M) by set_solver. subst. apply wt_nil.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + simpl in Hin. apply elem_of_app in Hin. destruct Hin as [Hin | Hin].
      * eapply wt_tau; [apply lts_choiceL; apply lts_tau |].
        apply IH; [simpl; lia | exact H1 | exact Hin].
      * eapply wt_tau; [apply lts_choiceR; apply lts_tau |].
        apply IH; [simpl; lia | exact H2 | exact Hin].
Qed.

Lemma leaves_wt_cons : forall M, tau_nf M -> forall mu s r,
  (g M) ⟹[mu :: s] r ->
  exists A p, A ∈ leaves M /\ lts (g A) (ActExt mu) p /\ p ⟹[s] r.
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HM mu s r Hwt.
  inversion HM as [? Hs | M1 M2 H1 H2]; subst.
  - destruct (wt_cons_stable (g M) r mu s (proj2 (gStable_iff M) Hs) Hwt) as (q & Hl & Hw).
    exists M, q. repeat split; [| exact Hl | exact Hw].
    rewrite leaves_eq. rewrite (proj2 (gStableB_spec M) Hs). set_solver.
  - assert (E : gStableB ((𝛕 • (g M1)) + (𝛕 • (g M2))) = false) by reflexivity.
    rewrite leaves_eq. rewrite E.
    inversion Hwt; subst.
    + inversion l; subst; inversion H5; subst.
      * destruct (IH M1 ltac:(simpl; lia) H1 mu s r w) as (A & p & Hin & Hl & Hw).
        exists A, p. repeat split; [apply elem_of_app; left; exact Hin | exact Hl | exact Hw].
      * destruct (IH M2 ltac:(simpl; lia) H2 mu s r w) as (A & p & Hin & Hl & Hw).
        exists A, p. repeat split; [apply elem_of_app; right; exact Hin | exact Hl | exact Hw].
    + exfalso. inversion l; subst; inversion H5.
Qed.

(** ** "[M] after [mu]", and the recursion's semantic engine

    [after M mu] lists every [mu]-reduct of every leaf — computable
    because VCCS's [gLts] instance gives [lts_set] as a [gset]. Wrapped
    in [ichoice] it realises exactly [M]'s behaviour after [mu]
    ([after_wt_stable]), and so may be plugged into [must_i_shift].

    [after_below_reduct] is the payoff and the whole point of this
    section: for any single [mu]-reduct [qa] of the right-hand side,

        g (ichoice (after M mu)) ⊑ₘᵤₛₜᵢ qa

    which is precisely the premise the completeness recursion needs
    before descending into a matched summand's continuation. The
    right-hand side needs no normal form and no stability: one
    transition [g N ⟶[mu] qa] suffices, since [wt_act] turns any run of
    [qa] into a run of [g N] over [mu :: s]. *)

Fixpoint after_list (ls : list gproc) (mu : ExtAct TypeOfActions) : list proc :=
match ls with
| [] => []
| A :: ls' => elements (lts_set (g A) (ActExt mu)) ++ after_list ls' mu
end.

Definition after (M : gproc) (mu : ExtAct TypeOfActions) : list proc :=
  after_list (leaves M) mu.

Lemma after_list_spec : forall ls mu p,
  p ∈ after_list ls mu <-> exists A, A ∈ ls /\ lts (g A) (ActExt mu) p.
Proof.
  induction ls as [|A ls IH]; intros mu p; simpl; split.
  - intro H. set_solver.
  - intros (B & Hin & _). set_solver.
  - intro H. apply elem_of_app in H. destruct H as [H | H].
    + exists A. split; [set_solver | apply lts_set_spec0; apply elem_of_elements; exact H].
    + apply IH in H. destruct H as (B & Hin & Hl).
      exists B. split; [apply elem_of_cons; right; exact Hin | exact Hl].
  - intros (B & Hin & Hl). apply elem_of_app.
    apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + subst. left. apply elem_of_elements.
      (* [simpl] has already unfolded [lts_set] into its [ActIn]/[ActOut]
         match, so [apply lts_set_spec1] no longer unifies; build the
         term and close by conversion instead. *)
      pose proof (lts_set_spec1 (g A) (ActExt mu) p Hl) as Hm. exact Hm.
    + right. apply IH. exists B. split; assumption.
Qed.

Lemma after_Static : forall M mu, gStatic M -> Forall Static (after M mu).
Proof.
  intros M mu HM. apply Forall_forall. intros p Hp.
  apply after_list_spec in Hp. destruct Hp as (A & Hin & Hl).
  eapply Static_preserved_by_lts; [| exact Hl].
  apply static_g. pose proof (leaves_gStatic M HM) as HF.
  rewrite Forall_forall in HF. apply HF. exact Hin.
Qed.

Lemma after_wt_stable : forall M mu s r p0 l, tau_nf M -> after M mu = p0 :: l -> r ↛ ->
  ((g (ichoice (after M mu))) ⟹[s] r <-> (g M) ⟹[mu :: s] r).
Proof.
  intros M mu s r p0 l HM Heq Hst. rewrite Heq. split.
  - intro Hwt. apply ichoice_wt_stable in Hwt; [| exact Hst].
    destruct Hwt as (p & Hin & Hwp).
    rewrite <- Heq in Hin. apply after_list_spec in Hin.
    destruct Hin as (A & HinA & Hl).
    eapply wt_push_nil_left; [apply leaves_reach; eassumption |].
    eapply wt_act; [exact Hl | exact Hwp].
  - intro Hwt. destruct (leaves_wt_cons M HM mu s r Hwt) as (A & p & HinA & Hl & Hwp).
    apply ichoice_wt_stable; [exact Hst |].
    exists p. split; [| exact Hwp].
    rewrite <- Heq. apply after_list_spec. exists A. split; assumption.
Qed.

Theorem after_below_reduct : forall M N mu p0 l qa,
  gStatic M -> tau_nf M -> Static qa ->
  after M mu = p0 :: l ->
  lts (g N) (ActExt mu) qa ->
  g M ⊑ₘᵤₛₜᵢ g N ->
  g (ichoice (after M mu)) ⊑ₘᵤₛₜᵢ qa.
Proof.
  intros M N mu p0 l qa HMst HM Hqa Heq Hl Hpre.
  apply must_i_shift with (p := g M) (q := g N) (a := mu).
  - apply static_g. exact HMst.
  - exact Hqa.
  - intros s r Hst. eapply after_wt_stable; eassumption.
  - intros s r Hst Hw. eapply wt_act; [exact Hl | exact Hw].
  - exact Hpre.
Qed.

(** Two [ichoice]s over lists with the same *elements* are [⊢]-equal —
    multiplicity and order are invisible, since both directions are just
    [ax_ichoice_glb] fed by [ax_ichoice_below]. This is what lets the
    set-based [after M mu] (built from [lts_set], so duplicate-free) be
    exchanged for a syntactically collected list of continuations, which
    is what [ax_input]'s omega rule needs. *)

Lemma ax_ichoice_same_elems : forall l l', l <> [] -> l' <> [] ->
  Forall Static l -> Forall Static l' ->
  (forall p, p ∈ l <-> p ∈ l') ->
  ax_pre (g (ichoice l)) (g (ichoice l')).
Proof.
  intros l l' Hne Hne' Hst Hst' Hiff.
  apply ax_ichoice_glb; [exact Hne' | exact Hst' |].
  intros p Hp. apply ax_ichoice_below; [exact Hst | apply Hiff; exact Hp].
Qed.

(** ** Syntactic continuations, and why they are needed

    [after M mu] is a list of *reducts*. That is enough for an output
    summand, whose continuation is a closed term. It is **not** enough
    for an input: [ax_input] is the omega rule
    [(∀v, ⊢ P^v ⊑ Q^v) -> ⊢ g (c?P) ⊑ g (c?Q)], so the left-hand side
    needs an *open* [P] whose every instance [P^v] is "M after [(c,v)?]".
    Such a [P] can only be built by collecting the leaves' input
    continuations **before** substitution — which is what [in_conts]
    does, and why it exists alongside [after].

    This is the same lesson as the earlier move from label-level to
    summand-level canonicity, one level further on: in a value-passing
    calculus the consumer is an omega rule, so anything the derivation
    must produce has to be phrased over *binders*, never over
    instantiated labels. *)

Fixpoint in_conts_g (A : gproc) (c : ChannelData) : list proc :=
match A with
| c' ? P => if decide (c' = c) then [P] else []
| A1 + A2 => in_conts_g A1 c ++ in_conts_g A2 c
| _ => []
end.

Fixpoint out_conts_g (A : gproc) (c : ChannelData) (v : ValueData) : list proc :=
match A with
| c' ! v' • P => if decide (c' = c) then (if decide (v' = v) then [P] else []) else []
| A1 + A2 => out_conts_g A1 c v ++ out_conts_g A2 c v
| _ => []
end.

Lemma in_conts_g_spec : forall A c v p,
  lts (g A) (ActExt (ActIn (c,v))) p <-> exists P, P ∈ in_conts_g A c /\ p = P^v.
Proof.
  intro A. induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IHA1 A2 IHA2 ];
    intros c v p; split; intro H; simpl in *.
  - inversion H.
  - destruct H as (P & HP & _). set_solver.
  - inversion H.
  - destruct H as (P & HP & _). set_solver.
  - inversion H; subst. exists P0. split; [| reflexivity].
    destruct (decide (c = c)); [set_solver | contradiction].
  - destruct H as (P & HP & Heq).
    destruct (decide (c0 = c)) as [Hc | Hc]; [| set_solver].
    subst. assert (P = P0) by set_solver. subst. apply lts_input.
  - inversion H.
  - destruct H as (P & HP & _). set_solver.
  - inversion H.
  - destruct H as (P & HP & _). set_solver.
  - inversion H; subst.
    + apply IHA1 in H4. destruct H4 as (P & HP & Heq).
      exists P. split; [apply elem_of_app; left; exact HP | exact Heq].
    + apply IHA2 in H4. destruct H4 as (P & HP & Heq).
      exists P. split; [apply elem_of_app; right; exact HP | exact Heq].
  - destruct H as (P & HP & Heq). apply elem_of_app in HP.
    destruct HP as [HP | HP].
    + apply lts_choiceL. apply IHA1. exists P. split; assumption.
    + apply lts_choiceR. apply IHA2. exists P. split; assumption.
Qed.

Lemma out_conts_g_spec : forall A c v p,
  lts (g A) (ActExt (ActOut (c,v))) p <-> p ∈ out_conts_g A c v.
Proof.
  intro A. induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IHA1 A2 IHA2 ];
    intros c v p; split; intro H; simpl in *.
  - inversion H.
  - set_solver.
  - inversion H.
  - set_solver.
  - inversion H.
  - set_solver.
  - inversion H; subst.
    destruct (decide (c = c)); [| contradiction].
    destruct (decide (v = v)); [set_solver | contradiction].
  - destruct (decide (c0 = c)) as [Hc | Hc]; [| set_solver].
    destruct (decide (v0 = v)) as [Hv | Hv]; [| set_solver].
    subst. assert (p = P0) by set_solver. subst. apply lts_output.
  - inversion H.
  - set_solver.
  - inversion H; subst.
    + apply elem_of_app. left. apply IHA1. exact H4.
    + apply elem_of_app. right. apply IHA2. exact H4.
  - apply elem_of_app in H. destruct H as [H | H].
    + apply lts_choiceL. apply IHA1. exact H.
    + apply lts_choiceR. apply IHA2. exact H.
Qed.

(** Substitution distributes over [ichoice] — it only ever builds [𝛕]
    guards and sums, neither of which binds, so the index stays at [0].
    Stated at the [gproc] level: at [proc] level the [g] coercion would
    have to be inverted before [rewrite] could fire. *)

Lemma subst_ichoice : forall l v,
  subst_in_gproc 0 v (ichoice l) = ichoice (map (fun P => P^v) l).
Proof.
  induction l as [|p l IH]; intro v; simpl; [reflexivity |].
  destruct l as [|p2 l2]; simpl; [reflexivity |].
  specialize (IH v). simpl in IH. rewrite IH. reflexivity.
Qed.

Lemma subst_ichoice_proc : forall l v,
  (g (ichoice l))^v = g (ichoice (map (fun P => P^v) l)).
Proof. intros l v. simpl. rewrite subst_ichoice. reflexivity. Qed.

Lemma elem_of_map_proc : forall (f : proc -> proc) l p,
  p ∈ map f l <-> exists q, q ∈ l /\ p = f q.
Proof.
  intros f l p. induction l as [|a l IH]; simpl; split.
  - intro H. set_solver.
  - intros (q & Hq & _). set_solver.
  - intro H. apply elem_of_cons in H. destruct H as [Heq | H].
    + exists a. split; [set_solver | exact Heq].
    + apply IH in H. destruct H as (q & Hq & Heq).
      exists q. split; [apply elem_of_cons; right; exact Hq | exact Heq].
  - intros (q & Hq & Heq). apply elem_of_cons in Hq. destruct Hq as [He | Hq].
    + subst. apply elem_of_cons. left. reflexivity.
    + apply elem_of_cons. right. apply IH. exists q. split; assumption.
Qed.

Fixpoint in_conts_list (ls : list gproc) (c : ChannelData) : list proc :=
match ls with [] => [] | A :: ls' => in_conts_g A c ++ in_conts_list ls' c end.

Fixpoint out_conts_list (ls : list gproc) (c : ChannelData) (v : ValueData) : list proc :=
match ls with [] => [] | A :: ls' => out_conts_g A c v ++ out_conts_list ls' c v end.

Definition in_conts (M : gproc) (c : ChannelData) : list proc :=
  in_conts_list (leaves M) c.
Definition out_conts (M : gproc) (c : ChannelData) (v : ValueData) : list proc :=
  out_conts_list (leaves M) c v.

Lemma in_conts_list_spec : forall ls c p,
  p ∈ in_conts_list ls c <-> exists A, A ∈ ls /\ p ∈ in_conts_g A c.
Proof.
  induction ls as [|A ls IH]; intros c p; simpl; split.
  - intro H. set_solver.
  - intros (B & HB & _). set_solver.
  - intro H. apply elem_of_app in H. destruct H as [H | H].
    + exists A. split; [set_solver | exact H].
    + apply IH in H. destruct H as (B & HB & H).
      exists B. split; [apply elem_of_cons; right; exact HB | exact H].
  - intros (B & HB & H). apply elem_of_app. apply elem_of_cons in HB.
    destruct HB as [Heq | HB]; [subst; left; exact H |].
    right. apply IH. exists B. split; assumption.
Qed.

Lemma out_conts_list_spec : forall ls c v p,
  p ∈ out_conts_list ls c v <-> exists A, A ∈ ls /\ p ∈ out_conts_g A c v.
Proof.
  induction ls as [|A ls IH]; intros c v p; simpl; split.
  - intro H. set_solver.
  - intros (B & HB & _). set_solver.
  - intro H. apply elem_of_app in H. destruct H as [H | H].
    + exists A. split; [set_solver | exact H].
    + apply IH in H. destruct H as (B & HB & H).
      exists B. split; [apply elem_of_cons; right; exact HB | exact H].
  - intros (B & HB & H). apply elem_of_app. apply elem_of_cons in HB.
    destruct HB as [Heq | HB]; [subst; left; exact H |].
    right. apply IH. exists B. split; assumption.
Qed.

(** The bridge. Instantiating the syntactically collected input
    continuations at [v] gives exactly [M]'s [(c,v)?]-reducts (up to
    multiplicity, which [ax_ichoice_same_elems] renders harmless); the
    output case needs no substitution at all. *)

Lemma in_conts_after : forall M c v p,
  p ∈ map (fun P => P^v) (in_conts M c) <-> p ∈ after M (ActIn (c,v)).
Proof.
  intros M c v p. rewrite elem_of_map_proc. unfold in_conts, after.
  rewrite after_list_spec. split.
  - intros (q & Hq & Heq). apply in_conts_list_spec in Hq.
    destruct Hq as (A & HA & Hq).
    exists A. split; [exact HA | apply in_conts_g_spec; exists q; split; assumption].
  - intros (A & HA & Hl). apply in_conts_g_spec in Hl.
    destruct Hl as (P & HP & Heq).
    exists P. split; [| exact Heq].
    apply in_conts_list_spec. exists A. split; assumption.
Qed.

Lemma out_conts_after : forall M c v p,
  p ∈ out_conts M c v <-> p ∈ after M (ActOut (c,v)).
Proof.
  intros M c v p. unfold out_conts, after.
  rewrite after_list_spec, out_conts_list_spec. split.
  - intros (A & HA & H). exists A. split; [exact HA | apply out_conts_g_spec; exact H].
  - intros (A & HA & H). exists A. split; [exact HA | apply out_conts_g_spec; exact H].
Qed.

(** ** The premise for one matched summand

    For each summand of the right-hand side, the completeness recursion
    needs its continuation to dominate "[M] after that action". These two
    lemmas package exactly that, and are the last semantic step before
    the assembly: everything after them is derivation-building.

    The right-hand side is only ever used through [summand_lts_in] /
    [summand_lts_out] — one transition of [g N], nothing more. No normal
    form, no canonicity, no stability is required of [N] here. *)

Lemma summand_lts_in : forall N c P v, (c ? P) ∈ summands N ->
  lts (g N) (ActExt (ActIn (c,v))) (P^v).
Proof.
  intro N. induction N as [ | | c0 P0 | c0 v0 P0 | P0 | N1 IH1 N2 IH2 ];
    intros c P v Hin; simpl in Hin.
  - set_solver.
  - set_solver.
  - assert (Heq : (c0 ? P0) = (c ? P)) by set_solver.
    injection Heq as Hc HP. subst. apply lts_input.
  - set_solver.
  - set_solver.
  - apply elem_of_app in Hin. destruct Hin as [H|H].
    + apply lts_choiceL. apply IH1. exact H.
    + apply lts_choiceR. apply IH2. exact H.
Qed.

Lemma summand_lts_out : forall N c v P, (c ! v • P) ∈ summands N ->
  lts (g N) (ActExt (ActOut (c,v))) P.
Proof.
  intro N. induction N as [ | | c0 P0 | c0 v0 P0 | P0 | N1 IH1 N2 IH2 ];
    intros c v P Hin; simpl in Hin.
  - set_solver.
  - set_solver.
  - set_solver.
  - assert (Heq : (c0 ! v0 • P0) = (c ! v • P)) by set_solver.
    injection Heq as Hc Hv HP. subst. apply lts_output.
  - set_solver.
  - apply elem_of_app in Hin. destruct Hin as [H|H].
    + apply lts_choiceL. apply IH1. exact H.
    + apply lts_choiceR. apply IH2. exact H.
Qed.

Lemma ichoice_same_elems_pre : forall l l', l <> [] -> l' <> [] ->
  Forall Static l -> Forall Static l' -> (forall p, p ∈ l <-> p ∈ l') ->
  g (ichoice l) ⊑ₘᵤₛₜᵢ g (ichoice l').
Proof.
  intros l l' Hne Hne' Hst Hst' Hiff.
  apply soundness_ax;
    [apply static_g; apply ichoice_gStatic; exact Hst
    | apply static_g; apply ichoice_gStatic; exact Hst'
    | apply ax_ichoice_same_elems; assumption].
Qed.

(** [Static]-ness of the collected continuations comes for free through
    [after], whose members are reducts of [Static] leaves. *)

Lemma out_conts_Static : forall M c v, gStatic M -> Forall Static (out_conts M c v).
Proof.
  intros M c v HM. apply Forall_forall. intros p Hp.
  pose proof (after_Static M (ActOut (c,v)) HM) as HF.
  rewrite Forall_forall in HF. apply HF. apply out_conts_after. exact Hp.
Qed.

Lemma in_conts_subst_Static : forall M c v, gStatic M ->
  Forall Static (map (fun P => P^v) (in_conts M c)).
Proof.
  intros M c v HM. apply Forall_forall. intros p Hp.
  pose proof (after_Static M (ActIn (c,v)) HM) as HF.
  rewrite Forall_forall in HF. apply HF. apply in_conts_after. exact Hp.
Qed.

Lemma out_cont_below : forall M N c v Q p0 l,
  gStatic M -> tau_nf M -> Static Q ->
  out_conts M c v = p0 :: l ->
  (c ! v • Q) ∈ summands N ->
  g M ⊑ₘᵤₛₜᵢ g N ->
  g (ichoice (out_conts M c v)) ⊑ₘᵤₛₜᵢ Q.
Proof.
  intros M N c v Q p0 l HM Hnf HQ Heq Hin Hpre.
  assert (Hp0 : p0 ∈ after M (ActOut (c,v)))
    by (apply out_conts_after; rewrite Heq; apply elem_of_cons; left; reflexivity).
  destruct (after M (ActOut (c,v))) as [|q0 l'] eqn:Ea; [set_solver |].
  transitivity (g (ichoice (after M (ActOut (c,v))))).
  - rewrite Ea. apply ichoice_same_elems_pre.
    + rewrite Heq. discriminate.
    + discriminate.
    + apply out_conts_Static; exact HM.
    + rewrite <- Ea. apply after_Static; exact HM.
    + intro p. rewrite <- Ea. apply out_conts_after.
  - eapply after_below_reduct; try eassumption.
    apply summand_lts_out. exact Hin.
Qed.

(** The input analogue, and the reason [in_conts] had to be collected
    before substitution: the conclusion is stated at an *arbitrary* [v],
    which is exactly the shape [ax_input]'s omega rule consumes. *)

Lemma in_cont_below : forall M N c Q v p0 l,
  gStatic M -> tau_nf M -> Static (Q^v) ->
  in_conts M c = p0 :: l ->
  (c ? Q) ∈ summands N ->
  g M ⊑ₘᵤₛₜᵢ g N ->
  (g (ichoice (in_conts M c)))^v ⊑ₘᵤₛₜᵢ (Q^v).
Proof.
  intros M N c Q v p0 l HM Hnf HQ Heq Hin Hpre.
  rewrite subst_ichoice_proc.
  assert (Hp0 : (p0^v) ∈ after M (ActIn (c,v))).
  { apply in_conts_after. apply elem_of_map_proc. exists p0.
    split; [rewrite Heq; apply elem_of_cons; left; reflexivity | reflexivity]. }
  destruct (after M (ActIn (c,v))) as [|q0 l'] eqn:Ea; [set_solver |].
  transitivity (g (ichoice (after M (ActIn (c,v))))).
  - rewrite Ea. apply ichoice_same_elems_pre.
    + rewrite Heq. discriminate.
    + discriminate.
    + apply in_conts_subst_Static; exact HM.
    + rewrite <- Ea. apply after_Static; exact HM.
    + intro p. rewrite <- Ea. apply in_conts_after.
  - eapply after_below_reduct; try eassumption.
    apply summand_lts_in. exact Hin.
Qed.

(** ** The mirror sum

    Given the right-hand side's stable sum, the left-hand sum the
    derivation aims at is built *from the right-hand side's own
    summands*: each guard is kept and its continuation replaced by the
    corresponding "[M] after that action". [ax_match_lists] then reduces
    [⊢ g (mirror) ⊑ g N] to the two premises [out_cont_below] and
    [in_cont_below] supply, one per summand.

    Building the mirror from [N] rather than from [M]'s leaves has a
    pleasant consequence: **[N] need not be canonical**. If [N] has two
    summands on the same action, both are mirrored to the same guard,
    and each pair is discharged by the same lemma at its own summand —
    the earlier worry about forcing a pairing simply does not arise on
    this side. *)

Lemma in_conts_g_Static : forall A c, gStatic A -> Forall Static (in_conts_g A c).
Proof.
  intro A. induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IH1 A2 IH2 ];
    intros c HA; simpl; try constructor.
  - destruct (decide (c0 = c)); [| constructor].
    inversion HA; subst. constructor; [assumption | constructor].
  - inversion HA; subst. apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
Qed.

Lemma in_conts_Static : forall M c, gStatic M -> Forall Static (in_conts M c).
Proof.
  intros M c HM. unfold in_conts.
  pose proof (leaves_gStatic M HM) as HF.
  induction (leaves M) as [|A ls IH]; simpl; [constructor |].
  inversion HF as [|? ? HA HF']; subst.
  apply Forall_app. split; [apply in_conts_g_Static; exact HA | apply IH; exact HF'].
Qed.

Lemma Forall2_map_self : forall (f : gproc -> gproc) (R : gproc -> gproc -> Prop) l,
  (forall a, a ∈ l -> R (f a) a) -> Forall2 R (map f l) l.
Proof.
  induction l as [|a l IH]; intro H; simpl; [constructor |].
  constructor.
  - apply H. apply elem_of_cons. left. reflexivity.
  - apply IH. intros b Hb. apply H. apply elem_of_cons. right. exact Hb.
Qed.

Definition mirror_summand (M : gproc) (n : gproc) : gproc :=
match n with
| c ? Q => c ? (g (ichoice (in_conts M c)))
| c ! v • Q => c ! v • (g (ichoice (out_conts M c v)))
| _ => n
end.

Lemma mirror_summand_gStatic : forall M n, gStatic M -> gStatic n ->
  gStatic (mirror_summand M n).
Proof.
  intros M n HM Hn.
  destruct n as [ | | c Q | c v Q | Q | N1 N2 ]; simpl; try exact Hn.
  - constructor. apply static_g. apply ichoice_gStatic. apply in_conts_Static. exact HM.
  - constructor. apply static_g. apply ichoice_gStatic. apply out_conts_Static. exact HM.
Qed.

Lemma mirror_summand_gStable : forall M n, gStable n -> gStable (mirror_summand M n).
Proof.
  intros M n Hn. destruct n as [ | | c Q | c v Q | Q | N1 N2 ]; simpl in *; exact Hn.
Qed.

(** ** The recursion's measure: a bound on trace length

    The outer recursion cannot be measured by [size]. Its left-hand
    argument is unbounded (it is an [ichoice] over [M]'s leaves), and its
    right-hand argument is a continuation of the *normal form* of the
    original [q] — and normalisation is not size-decreasing, so neither
    [size q] nor [size (g N)] survives a step.

    A **bound on the length of [q]'s traces** does survive, for one
    reason: it is a semantic quantity. Two [⊑ₘᵤₛₜᵢ]-related [Static]
    processes have comparable trace sets ([must_i_trace_incl]), so
    normalising the right-hand side cannot lengthen its traces — whereas
    it can freely enlarge the term. And each matched summand consumes one
    visible action, so the bound strictly drops at every recursive call
    ([tbound_step]).

    The [⊕]-layer is different: descending into a branch of an internal
    choice consumes no visible action, so the bound is unchanged there
    ([tbound_tau]) and that layer must be measured by [size (g N)]
    instead. The two together are lexicographic — [tbound] outermost,
    [size] inner — which is why the assembly is a nat induction on the
    bound with a well-founded [size] induction inside.

    [must_i_trace_incl] is the load-bearing step, and it is where the
    [Static] fragment pays off twice: [bhv_pre_cond2] only ever speaks
    about *stable* reducts, but in a non-divergent calculus every
    reachable state reaches a stable one ([wt_stable_reach], from
    [Static_terminate]) without extending the trace, so a bound on
    traces-to-stable-states bounds all traces. *)

Lemma wt_length_bound : forall s p r, Static p -> p ⟹[s] r -> (length s <= size p)%nat.
Proof.
  intros s p r Hst Hwt. revert Hst.
  induction Hwt as [p | s p q t Hl Hwt IH | mu s p q t Hl Hwt IH]; intro Hst; simpl.
  - lia.
  - assert (Hq : Static q) by (eapply Static_preserved_by_lts; eassumption).
    assert (Hlt : (size q < size p)%nat) by (eapply Static_lts_decrease; eassumption).
    specialize (IH Hq). lia.
  - assert (Hq : Static q) by (eapply Static_preserved_by_lts; eassumption).
    assert (Hlt : (size q < size p)%nat) by (eapply Static_lts_decrease; eassumption).
    specialize (IH Hq). lia.
Qed.

Lemma wt_stable_reach : forall r, Static r -> exists r', r ⟹[[]] r' /\ r' ↛.
Proof.
  intros r Hst. destruct (terminate_then_wt_refuses r (Static_terminate r Hst)) as (r' & Hw & Hs).
  exists r'. split; assumption.
Qed.

Lemma bhv_pre_trace_incl : forall (p q : proc), Static q -> Static p -> p ≼ₐₛ q ->
  forall s r, q ⟹[s] r -> exists p', p ⟹[s] p'.
Proof.
  intros p q Hq Hp (Hc1 & Hc2) s r Hwt.
  assert (Hrst : Static r) by (eapply Static_preserved_by_wt; [exact Hq | exact Hwt]).
  destruct (wt_stable_reach r Hrst) as (r' & Hw' & Hs').
  destruct (Hc2 s r' (Static_converge s p Hp) (wt_push_nil_right q r r' s Hwt Hw') Hs')
    as (p' & Hwp & _ & _).
  exists p'. exact Hwp.
Qed.

Corollary must_i_trace_incl : forall (p q : proc), Static p -> Static q -> p ⊑ₘᵤₛₜᵢ q ->
  forall s r, q ⟹[s] r -> exists p', p ⟹[s] p'.
Proof.
  intros p q Hp Hq Hpre. apply bhv_pre_trace_incl; [exact Hq | exact Hp |].
  apply must_iff_acceptance_set_VCCS_without_toFW. exact Hpre.
Qed.

Definition tbound (n : nat) (q : proc) : Prop :=
  forall s r, q ⟹[s] r -> (length s <= n)%nat.

Lemma Static_tbound : forall p, Static p -> tbound (size p) p.
Proof. intros p Hst s r Hwt. eapply wt_length_bound; eassumption. Qed.

Lemma tbound_transfer : forall n (p q : proc), Static p -> Static q ->
  p ⊑ₘᵤₛₜᵢ q -> tbound n p -> tbound n q.
Proof.
  intros n p q Hp Hq Hpre Hb s r Hwt.
  destruct (must_i_trace_incl p q Hp Hq Hpre s r Hwt) as (p' & Hwp).
  eapply Hb; exact Hwp.
Qed.

Lemma tbound_tau : forall n (p p' : proc), lts p τ p' -> tbound n p -> tbound n p'.
Proof. intros n p p' Hl Hb s r Hwt. eapply Hb. eapply wt_tau; eassumption. Qed.

Lemma tbound_step : forall n N A mu Q, tau_nf N -> A ∈ leaves N ->
  lts (g A) (ActExt mu) Q -> tbound (S n) (g N) -> tbound n Q.
Proof.
  intros n N A mu Q Hnf Hin Hl Hb s r Hwt.
  assert (Hg : (g N) ⟹[mu :: s] r).
  { eapply wt_push_nil_left; [apply leaves_reach; eassumption |].
    eapply wt_act; [exact Hl | exact Hwt]. }
  pose proof (Hb (mu :: s) r Hg) as H. simpl in H. lia.
Qed.

(** [ichoice] turns list concatenation into binary internal choice —
    both directions, purely from the two n-ary laws. Needed at the
    [⊕]-nodes of the assembly, where the two branches' continuations at
    a shared action have to be merged into the single [ichoice] the
    mirror sum names. *)

Lemma ax_ichoice_app_l : forall l1 l2, l1 <> [] -> l2 <> [] ->
  Forall Static l1 -> Forall Static l2 ->
  ax_pre (g (ichoice (l1 ++ l2)))
         (g ((𝛕 • (g (ichoice l1))) + (𝛕 • (g (ichoice l2))))).
Proof.
  intros l1 l2 H1 H2 Hs1 Hs2.
  assert (Hs : Forall Static (l1 ++ l2)) by (apply Forall_app; split; assumption).
  apply ax_int_glb.
  - apply ax_ichoice_glb; [exact H1 | exact Hs1 |].
    intros p Hp. apply ax_ichoice_below; [exact Hs | apply elem_of_app; left; exact Hp].
  - apply ax_ichoice_glb; [exact H2 | exact Hs2 |].
    intros p Hp. apply ax_ichoice_below; [exact Hs | apply elem_of_app; right; exact Hp].
Qed.

Lemma ax_ichoice_app_r : forall l1 l2, l1 <> [] -> l2 <> [] ->
  Forall Static l1 -> Forall Static l2 ->
  ax_pre (g ((𝛕 • (g (ichoice l1))) + (𝛕 • (g (ichoice l2)))))
         (g (ichoice (l1 ++ l2))).
Proof.
  intros l1 l2 H1 H2 Hs1 Hs2.
  assert (Hs : Forall Static (l1 ++ l2)).
  { apply Forall_app; split; assumption. }
  apply ax_ichoice_glb.
  - destruct l1; [contradiction | discriminate].
  - exact Hs.
  - intros p Hp. apply elem_of_app in Hp. destruct Hp as [Hp | Hp].
    + eapply ax_trans; [apply ax_int_l | apply ax_ichoice_below; assumption].
    + eapply ax_trans; [apply ax_int_r | apply ax_ichoice_below; assumption].
Qed.

(** ** The mirror, parametrised by an action set

    [mirror_summand] above reads the guards off [N]. The derivation of
    [⊢ g M ⊑ g (mirror …)] runs by induction on [M]'s own [⊕]-tree, and
    at an [⊕]-node the two branches contribute *different* action sets —
    so the mirror has to be parametrised by the set explicitly rather
    than read off a right-hand side. [mirror M S] is that version;
    [mirror_summand] is the special case where [S] is [N]'s action set.

    An action is a key [(c, None)] (input on [c]) or [(c, Some v)]
    (output of [v] on [c]) — the same granularity as [gact]
    ([VCCS_Canonical.v]), which is exactly the level at which
    canonicity was stated after the correction from label-level to
    summand-level. *)

Lemma elem_of_map_any : forall (A B : Type) (f : A -> B) (l : list A) (b : B),
  b ∈ map f l <-> exists a, a ∈ l /\ b = f a.
Proof.
  intros A B f l b. induction l as [|a l IH]; simpl; split.
  - intro H. set_solver.
  - intros (x & Hx & _). set_solver.
  - intro H. apply elem_of_cons in H. destruct H as [Heq | H].
    + exists a. split; [set_solver | exact Heq].
    + apply IH in H. destruct H as (x & Hx & Heq).
      exists x. split; [apply elem_of_cons; right; exact Hx | exact Heq].
  - intros (x & Hx & Heq). apply elem_of_cons in Hx. destruct Hx as [He | Hx].
    + subst. apply elem_of_cons. left. reflexivity.
    + apply elem_of_cons. right. apply IH. exists x. split; assumption.
Qed.

Definition act_key : Type := (ChannelData * option ValueData)%type.

Definition conts_at (M : gproc) (k : act_key) : list proc :=
match k with
| (c, None) => in_conts M c
| (c, Some v) => out_conts M c v
end.

Definition mirror_act (M : gproc) (k : act_key) : gproc :=
match k with
| (c, None) => c ? (g (ichoice (in_conts M c)))
| (c, Some v) => c ! v • (g (ichoice (out_conts M c v)))
end.

Definition mirror (M : gproc) (S : list act_key) : gproc :=
  rebuild (map (mirror_act M) S).

Lemma conts_at_Static : forall M k, gStatic M -> Forall Static (conts_at M k).
Proof.
  intros M (c, [v|]) HM; simpl.
  - apply out_conts_Static; exact HM.
  - apply in_conts_Static; exact HM.
Qed.

Lemma mirror_act_gStatic : forall M k, gStatic M -> gStatic (mirror_act M k).
Proof.
  intros M (c, [v|]) HM; simpl;
    constructor; apply static_g; apply ichoice_gStatic;
    [apply out_conts_Static | apply in_conts_Static]; exact HM.
Qed.

Lemma mirror_act_gStable : forall M k, gStable (mirror_act M k).
Proof. intros M (c, [v|]); simpl; exact I. Qed.

Lemma mirror_act_leaf : forall M k, summands (mirror_act M k) = [mirror_act M k].
Proof. intros M (c, [v|]); reflexivity. Qed.

Lemma mirror_gStatic : forall M S, gStatic M -> gStatic (mirror M S).
Proof.
  intros M S HM. apply rebuild_gStatic. apply Forall_forall. intros a Ha.
  apply elem_of_map_any in Ha. destruct Ha as (k & _ & Heq). subst.
  apply mirror_act_gStatic. exact HM.
Qed.

Lemma mirror_gStable : forall M S, gStable (mirror M S).
Proof.
  intros M S. apply gStable_rebuild. apply Forall_forall. intros a Ha.
  apply elem_of_map_any in Ha. destruct Ha as (k & _ & Heq). subst.
  apply mirror_act_gStable.
Qed.

Lemma summands_rebuild_leaves : forall l, Forall (fun a => summands a = [a]) l ->
  summands (rebuild l) = l ++ [𝟘].
Proof.
  induction l as [|a l IH]; intro H; simpl; [reflexivity |].
  inversion H as [|? ? Ha H']; subst.
  rewrite Ha. simpl. rewrite (IH H'). reflexivity.
Qed.

Lemma summands_mirror : forall M S,
  summands (mirror M S) = map (mirror_act M) S ++ [𝟘].
Proof.
  intros M S. unfold mirror. apply summands_rebuild_leaves.
  apply Forall_forall. intros a Ha. apply elem_of_map_any in Ha.
  destruct Ha as (k & _ & Heq). subst. apply mirror_act_leaf.
Qed.

(** The base cases of the mirror derivation.

    [ichoice [p] ≂ p] is derivable *because* the singleton case was
    defined as [𝛕•p + 𝛕•p]: [ax_int_l] one way, [ax_int_glb] on two
    copies of [ax_refl] the other. With the obvious [𝛕•p] it would have
    needed Milner's first [𝛕]-law, which this system does not have.

    On a *stable* sum, [leaves] is the singleton [[A]], so [in_conts] and
    [out_conts] collapse to their per-guard versions and a single guard
    mirrors to itself with its continuation wrapped in a one-element
    [ichoice]. *)

Lemma ax_ichoice_singleton_l : forall p, ax_pre (g (ichoice [p])) p.
Proof. intro p. simpl. apply ax_int_l. Qed.

Lemma ax_ichoice_singleton_r : forall p, ax_pre p (g (ichoice [p])).
Proof. intro p. simpl. apply ax_int_glb; apply ax_refl. Qed.

Lemma leaves_stable_self : forall A, gStable A -> leaves A = [A].
Proof.
  intros A H. rewrite leaves_eq. rewrite (proj2 (gStableB_spec A) H). reflexivity.
Qed.

Lemma in_conts_stable : forall A c, gStable A -> in_conts A c = in_conts_g A c.
Proof.
  intros A c H. unfold in_conts. rewrite (leaves_stable_self A H). simpl.
  apply app_nil_r.
Qed.

Lemma out_conts_stable : forall A c v, gStable A -> out_conts A c v = out_conts_g A c v.
Proof.
  intros A c v H. unfold out_conts. rewrite (leaves_stable_self A H). simpl.
  apply app_nil_r.
Qed.

Lemma in_conts_guard : forall c P, in_conts (c ? P) c = [P].
Proof.
  intros c P. rewrite (in_conts_stable (c ? P) c I). simpl.
  destruct (decide (c = c)); [reflexivity | contradiction].
Qed.

Lemma out_conts_guard : forall c v P, out_conts (c ! v • P) c v = [P].
Proof.
  intros c v P. rewrite (out_conts_stable (c ! v • P) c v I). simpl.
  destruct (decide (c = c)); [| contradiction].
  destruct (decide (v = v)); [reflexivity | contradiction].
Qed.

(** The four base cases of the leaf induction. The trailing [𝟘] that
    [rebuild] always emits is removed by [cgr_choice_nil_rev] — note
    [ax_cgr]'s [Static] obligation is on its *target*, so it is the sum
    (with the [𝟘]) that has to be shown [Static], not the guard alone. *)

Lemma ax_mirror_guard_in : forall c P, Static P ->
  ax_pre (g (c ? P)) (g (mirror (c ? P) [(c, None)])).
Proof.
  intros c P HP. unfold mirror. simpl. rewrite in_conts_guard.
  assert (HI : Static (g (ichoice [P])))
    by (apply static_g; apply ichoice_gStatic; constructor; [exact HP | constructor]).
  eapply ax_trans with (q := g (c ? (g (ichoice [P])))).
  - apply ax_input. intro v. rewrite subst_ichoice_proc. simpl.
    apply ax_ichoice_singleton_r.
  - apply ax_cgr; [| apply cgr_choice_nil_rev].
    apply static_g. constructor; [constructor; exact HI | constructor].
Qed.

Lemma ax_mirror_guard_out : forall c v P, Static P ->
  ax_pre (g (c ! v • P)) (g (mirror (c ! v • P) [(c, Some v)])).
Proof.
  intros c v P HP. unfold mirror. simpl. rewrite out_conts_guard.
  assert (HI : Static (g (ichoice [P])))
    by (apply static_g; apply ichoice_gStatic; constructor; [exact HP | constructor]).
  eapply ax_trans with (q := g (c ! v • (g (ichoice [P])))).
  - apply ax_output. apply ax_ichoice_singleton_r.
  - apply ax_cgr; [| apply cgr_choice_nil_rev].
    apply static_g. constructor; [constructor; exact HI | constructor].
Qed.

Lemma ax_mirror_success : ax_pre (g ①) (g (mirror ① [])).
Proof. unfold mirror. simpl. apply ax_success_l. Qed.

Lemma ax_mirror_nil : ax_pre (g 𝟘) (g (mirror 𝟘 [])).
Proof. unfold mirror. simpl. apply ax_refl. Qed.

(** ** Half the leaf case: wrapping every continuation in an [ichoice]

    The leaf case of the mirror derivation splits cleanly in two. This
    is the first half, and it needs no action-set bookkeeping at all:
    replace each summand's continuation [P] by the one-element
    [ichoice [P]], summand by summand. Since the two sums then have the
    *same* summand list up to that pointwise change, [ax_match_lists]
    applies directly, and each pair is one of the four base cases —
    [ax_success_l] for [①], [ax_refl] for [𝟘], [ax_input]/[ax_output]
    composed with [ax_ichoice_singleton_r] for the guards.

    What remains after this is purely a merge: every summand now has the
    uniform shape "guard on [k], continuation [ichoice l]", and summands
    sharing a [k] have to be collapsed into one with the concatenated
    list — which is exactly what [ax_collapse_*_anywhere] plus
    [ax_ichoice_app_r] do in one step. *)

Lemma summands_nonempty : forall M, summands M <> [].
Proof.
  induction M; simpl; try discriminate.
  intro H. apply app_eq_nil in H. destruct H as (H1 & _). apply IHM1. exact H1.
Qed.

Lemma gStable_summands : forall A, gStable A -> forall a, a ∈ summands A -> gStable a.
Proof.
  induction A; intros HA a Ha; simpl in Ha, HA.
  - assert (a = ①) by set_solver. subst. exact I.
  - assert (a = 𝟘) by set_solver. subst. exact I.
  - assert (a = c ? p) by set_solver. subst. exact I.
  - assert (a = c ! v • p) by set_solver. subst. exact I.
  - contradiction.
  - destruct HA as (H1 & H2). apply elem_of_app in Ha. destruct Ha as [H|H].
    + eapply IHA1; eassumption.
    + eapply IHA2; eassumption.
Qed.

Lemma Forall2_self_map : forall (f : gproc -> gproc) (R : gproc -> gproc -> Prop) l,
  (forall a, a ∈ l -> R a (f a)) -> Forall2 R l (map f l).
Proof.
  induction l as [|a l IH]; intro H; simpl; [constructor |].
  constructor.
  - apply H. apply elem_of_cons. left. reflexivity.
  - apply IH. intros b Hb. apply H. apply elem_of_cons. right. exact Hb.
Qed.

Definition wrap_summand (a : gproc) : gproc :=
match a with
| c ? P => c ? (g (ichoice [P]))
| c ! v • P => c ! v • (g (ichoice [P]))
| _ => 𝟘
end.

Lemma wrap_summand_gStatic : forall a, gStatic a -> gStatic (wrap_summand a).
Proof.
  intros a Ha. destruct a as [ | | c P | c v P | P | A1 A2 ]; simpl.
  - constructor.
  - constructor.
  - inversion Ha; subst. constructor. apply static_g. constructor; constructor; assumption.
  - inversion Ha; subst. constructor. apply static_g. constructor; constructor; assumption.
  - constructor.
  - constructor.
Qed.

Lemma wrap_summand_gStable : forall a, gStable (wrap_summand a).
Proof. intro a. destruct a as [ | | c P | c v P | P | A1 A2 ]; simpl; exact I. Qed.

(** The [+] case is impossible for a *leaf*: [summands (A1 + A2)] is the
    concatenation of two non-empty lists, so it is never a singleton. *)

Lemma ax_wrap_summand : forall a, gStatic a -> gStable a -> summands a = [a] ->
  ax_pre (g a) (g (wrap_summand a)).
Proof.
  intros a Ha Hst Hleaf.
  destruct a as [ | | c P | c v P | P | A1 A2 ]; simpl.
  - apply ax_success_l.
  - apply ax_refl.
  - apply ax_input. intro v. simpl. apply ax_int_glb; apply ax_refl.
  - apply ax_output. simpl. apply ax_int_glb; apply ax_refl.
  - simpl in Hst. contradiction.
  - exfalso. simpl in Hleaf.
    destruct (summands A1) as [|x l1] eqn:E1; [apply (summands_nonempty A1 E1) |].
    destruct (summands A2) as [|y l2] eqn:E2; [apply (summands_nonempty A2 E2) |].
    simpl in Hleaf. injection Hleaf as _ Hl.
    apply app_eq_nil in Hl. destruct Hl as (_ & H2). discriminate H2.
Qed.

Definition wrapsum (A : gproc) : gproc := rebuild (map wrap_summand (summands A)).

Lemma ax_wrapsum : forall A, gStatic A -> gStable A -> ax_pre (g A) (g (wrapsum A)).
Proof.
  intros A HA Hst. unfold wrapsum.
  assert (HF : forall x, x ∈ summands A -> gStatic x).
  { pose proof (summands_gStatic A HA) as H. rewrite Forall_forall in H. exact H. }
  eapply ax_trans;
    [apply ax_cgr;
       [apply static_g; apply rebuild_gStatic; apply summands_gStatic; exact HA
       | apply summands_cgr] |].
  apply ax_match_lists.
  - apply summands_gStatic. exact HA.
  - apply Forall_forall. intros a Ha. apply elem_of_map_any in Ha.
    destruct Ha as (b & Hb & Heq). subst. apply wrap_summand_gStatic. apply HF. exact Hb.
  - apply Forall_forall. intros a Ha. eapply gStable_summands; eassumption.
  - apply Forall_forall. intros a Ha. apply elem_of_map_any in Ha.
    destruct Ha as (b & Hb & Heq). subst. apply wrap_summand_gStable.
  - apply Forall2_self_map. intros a Ha. apply ax_wrap_summand.
    + apply HF. exact Ha.
    + eapply gStable_summands; eassumption.
    + pose proof (summands_leaves A) as HL. rewrite Forall_forall in HL.
      apply HL. exact Ha.
Qed.

(** ** The merge step

    After [ax_wrapsum] every summand is a [kguard] — a guard on some
    action key carrying an [ichoice] continuation — so collapsing two
    that share a key is a single, uniform step: [ax_collapse_*_anywhere]
    turns them into one guard whose continuation is the binary internal
    choice of the two [ichoice]s, and [ax_ichoice_app_r] flattens that
    into the [ichoice] of the concatenated list.

    The input case is the one with content: the collapse happens *under
    the value binder*, so the equality has to hold at every [v], and it
    does because [subst_ichoice] pushes the substitution through the
    [ichoice] and [map_app] splits it back along the concatenation.
    That is the third time the same design point pays: continuations
    collected before substitution, laws stated at an arbitrary [v]. *)

Definition kguard (k : act_key) (l : list proc) : gproc :=
match k with
| (c, None) => c ? (g (ichoice l))
| (c, Some v) => c ! v • (g (ichoice l))
end.

Lemma Forall_Static_subst : forall l v, Forall Static l ->
  Forall Static (map (fun P => P^v) l).
Proof.
  intros l v H. apply Forall_forall. intros p Hp.
  apply elem_of_map_any in Hp. destruct Hp as (q & Hq & Heq). subst.
  apply Static_subst. rewrite Forall_forall in H. apply H. exact Hq.
Qed.

Lemma map_nonempty : forall (A B : Type) (f : A -> B) (l : list A),
  l <> [] -> map f l <> [].
Proof. intros A B f l H. destruct l; [contradiction | discriminate]. Qed.

Theorem ax_merge_anywhere : forall M k l1 l2 l,
  gStatic M -> l1 <> [] -> l2 <> [] -> Forall Static l1 -> Forall Static l2 ->
  Forall gStatic l ->
  Permutation (summands M) (kguard k l1 :: kguard k l2 :: l) ->
  ax_pre (g M) (g (kguard k (l1 ++ l2) + rebuild l)).
Proof.
  intros M (c, [v0|]) l1 l2 l HM H1 H2 Hs1 Hs2 Hl Hperm; simpl in Hperm |- *.
  - eapply ax_trans;
      [apply (proj1 (ax_collapse_output_anywhere M c v0 (g (ichoice l1)) (g (ichoice l2)) l
                       HM Hperm)) |].
    apply ax_choice_stable; [exact I | exact I |].
    apply ax_output. apply ax_ichoice_app_r; assumption.
  - eapply ax_trans;
      [apply (proj1 (ax_collapse_input_anywhere M c (g (ichoice l1)) (g (ichoice l2)) l
                       HM Hperm)) |].
    apply ax_choice_stable; [exact I | exact I |].
    apply ax_input. intro v.
    simpl. repeat rewrite subst_ichoice.
    rewrite map_app.
    apply (ax_ichoice_app_r (map (fun P => P^v) l1) (map (fun P => P^v) l2));
      [apply map_nonempty; exact H1 | apply map_nonempty; exact H2
       | apply Forall_Static_subst; exact Hs1 | apply Forall_Static_subst; exact Hs2].
Qed.

(** ** An association-list view of a stable sum

    Once every summand is a [kguard], the sum is determined by a list of
    (action key, continuation list) pairs, and the merge iteration is
    much easier to run there than on the syntax. [klist] extracts that
    view from a leaf's summands — dropping the [①]/[𝟘] summands, which
    carry no action — and [build] turns it back into a guarded sum.

    [ax_leaf_to_build] does the whole first half of the leaf case in one
    induction: each cons is either an [①] discarded via [ax_success_l]
    (then [cgr_choice_nil]), a [𝟘] discarded by [cgr] alone, or a guard
    whose continuation is wrapped in a singleton [ichoice]. The
    tail is rewritten by the induction hypothesis using the
    commute-then-[ax_choice_stable] trick from [ax_match_lists]. *)

Fixpoint klist (l : list gproc) : list (act_key * list proc) :=
match l with
| [] => []
| a :: l' =>
    match a with
    | c ? P => ((c, None), [P]) :: klist l'
    | c ! v • P => ((c, Some v), [P]) :: klist l'
    | _ => klist l'
    end
end.

Definition build (kl : list (act_key * list proc)) : gproc :=
  rebuild (map (fun p => kguard (fst p) (snd p)) kl).

Lemma build_gStable : forall kl, gStable (build kl).
Proof.
  intro kl. apply gStable_rebuild. apply Forall_forall. intros a Ha.
  apply elem_of_map_any in Ha. destruct Ha as ((k, l) & _ & Heq). subst.
  simpl. destruct k as (c, [v|]); simpl; exact I.
Qed.

Lemma kguard_gStatic : forall k l, Forall Static l -> gStatic (kguard k l).
Proof.
  intros (c, [v|]) l H; simpl; constructor; apply static_g; apply ichoice_gStatic; exact H.
Qed.

Lemma build_gStatic : forall kl,
  Forall (fun p => Forall Static (snd p)) kl -> gStatic (build kl).
Proof.
  intros kl H. apply rebuild_gStatic. apply Forall_forall. intros a Ha.
  apply elem_of_map_any in Ha. destruct Ha as ((k, l) & Hin & Heq). subst.
  simpl. apply kguard_gStatic.
  rewrite Forall_forall in H. apply (H (k, l) Hin).
Qed.

Lemma klist_Static : forall l, Forall gStatic l ->
  Forall (fun p => Forall Static (snd p)) (klist l).
Proof.
  induction l as [|a l IH]; intro H; simpl; [constructor |].
  inversion H as [|? ? Ha H']; subst.
  destruct a as [ | | c P | c v P | P | A1 A2 ]; try (apply IH; exact H').
  - inversion Ha; subst. constructor; [simpl; constructor; [assumption | constructor] |].
    apply IH; exact H'.
  - inversion Ha; subst. constructor; [simpl; constructor; [assumption | constructor] |].
    apply IH; exact H'.
Qed.

Lemma ax_leaf_to_build : forall l, Forall gStatic l -> Forall gStable l ->
  Forall (fun a => summands a = [a]) l ->
  ax_pre (g (rebuild l)) (g (build (klist l))).
Proof.
  induction l as [|a l IH]; intros Hst Hsb Hlf; simpl; [apply ax_refl |].
  inversion Hst as [|? ? Ha Hst']; subst.
  inversion Hsb as [|? ? Hb Hsb']; subst.
  inversion Hlf as [|? ? Hl Hlf']; subst.
  specialize (IH Hst' Hsb' Hlf').
  assert (Hrl : gStatic (rebuild l)) by (apply rebuild_gStatic; exact Hst').
  assert (Hbl : gStatic (build (klist l)))
    by (apply build_gStatic; apply klist_Static; exact Hst').
  assert (Hsrl : gStable (rebuild l)) by (apply gStable_rebuild; exact Hsb').
  destruct a as [ | | c P | c v P | P | A1 A2 ]; simpl.
  - eapply ax_trans; [apply (ax_choice_stable ① 𝟘 (rebuild l) I I ax_success_l) |].
    eapply ax_trans; [| exact IH].
    apply ax_cgr; [exact (static_g _ Hrl) |].
    transitivity (g (rebuild l + 𝟘)); [apply cgr_choice_com | apply cgr_choice_nil].
  - eapply ax_trans; [| exact IH].
    apply ax_cgr; [exact (static_g _ Hrl) |].
    transitivity (g (rebuild l + 𝟘)); [apply cgr_choice_com | apply cgr_choice_nil].
  - inversion Ha; subst.
    assert (Hk : gStatic (c ? (g (ichoice [P]))))
      by (constructor; apply static_g; constructor; constructor; assumption).
    eapply ax_trans;
      [apply (ax_choice_stable (c ? P) (c ? (g (ichoice [P]))) (rebuild l) I I);
       apply ax_input; intro w; simpl; apply ax_int_glb; apply ax_refl |].
    eapply ax_trans;
      [apply ax_cgr with (q := g (rebuild l + (c ? (g (ichoice [P])))));
         [apply static_g; constructor; assumption | apply cgr_choice_com] |].
    eapply ax_trans;
      [apply (ax_choice_stable (rebuild l) (build (klist l)) (c ? (g (ichoice [P]))));
         [exact Hsrl | apply build_gStable | exact IH] |].
    apply ax_cgr with (q := g ((c ? (g (ichoice [P]))) + build (klist l)));
      [apply static_g; constructor; assumption | apply cgr_choice_com].
  - inversion Ha; subst.
    assert (Hk : gStatic (c ! v • (g (ichoice [P]))))
      by (constructor; apply static_g; constructor; constructor; assumption).
    eapply ax_trans;
      [apply (ax_choice_stable (c ! v • P) (c ! v • (g (ichoice [P]))) (rebuild l) I I);
       apply ax_output; simpl; apply ax_int_glb; apply ax_refl |].
    eapply ax_trans;
      [apply ax_cgr with (q := g (rebuild l + (c ! v • (g (ichoice [P])))));
         [apply static_g; constructor; assumption | apply cgr_choice_com] |].
    eapply ax_trans;
      [apply (ax_choice_stable (rebuild l) (build (klist l)) (c ! v • (g (ichoice [P]))));
         [exact Hsrl | apply build_gStable | exact IH] |].
    apply ax_cgr with (q := g ((c ! v • (g (ichoice [P]))) + build (klist l)));
      [apply static_g; constructor; assumption | apply cgr_choice_com].
  - simpl in Hb. contradiction.
  - exfalso. simpl in Hl.
    destruct (summands A1) as [|x m1] eqn:E1; [apply (summands_nonempty A1 E1) |].
    destruct (summands A2) as [|y m2] eqn:E2; [apply (summands_nonempty A2 E2) |].
    simpl in Hl. injection Hl as _ Hl2.
    apply app_eq_nil in Hl2. destruct Hl2 as (_ & H2). discriminate H2.
Qed.

(** The merge step, lifted to the association-list view. The only
    friction is [rebuild]'s trailing [𝟘]: [ax_merge_anywhere] puts the
    untouched summands back with a [rebuild], which re-emits one, so the
    result carries two. [cgr_rebuild_snoc_nil] absorbs the extra. *)

Lemma kguard_leaf : forall k l, summands (kguard k l) = [kguard k l].
Proof. intros (c, [v|]) l; reflexivity. Qed.

Lemma summands_build : forall kl,
  summands (build kl) = map (fun p => kguard (fst p) (snd p)) kl ++ [𝟘].
Proof.
  intro kl. unfold build. apply summands_rebuild_leaves.
  apply Forall_forall. intros a Ha. apply elem_of_map_any in Ha.
  destruct Ha as ((k, l) & _ & Heq). subst. simpl. apply kguard_leaf.
Qed.

Lemma cgr_rebuild_snoc_nil : forall X, g (rebuild (X ++ [𝟘])) ≡* g (rebuild X).
Proof.
  intro X. transitivity (g (rebuild X + rebuild [𝟘])); [apply rebuild_app |].
  simpl. transitivity (g (rebuild X + 𝟘)).
  - apply cgr_fullchoice; [reflexivity | apply cgr_choice_nil].
  - apply cgr_choice_nil.
Qed.

Theorem ax_merge_klist : forall kl k l1 l2 rest,
  Forall (fun p => Forall Static (snd p)) kl -> l1 <> [] -> l2 <> [] ->
  Forall Static l1 -> Forall Static l2 ->
  Forall (fun p => Forall Static (snd p)) rest ->
  Permutation kl ((k, l1) :: (k, l2) :: rest) ->
  ax_pre (g (build kl)) (g (build ((k, l1 ++ l2) :: rest))).
Proof.
  intros kl k l1 l2 rest Hkl H1 H2 Hs1 Hs2 Hrest Hperm.
  set (kg := fun p : act_key * list proc => kguard (fst p) (snd p)).
  assert (Hpm : Permutation (summands (build kl))
                  (kguard k l1 :: kguard k l2 :: (map kg rest ++ [𝟘]))).
  { rewrite summands_build.
    change (kguard k l1 :: kguard k l2 :: (map kg rest ++ [𝟘]))
      with ((kg (k, l1) :: kg (k, l2) :: map kg rest) ++ [𝟘]).
    apply Permutation_app_tail. change (kg (k,l1) :: kg (k,l2) :: map kg rest)
      with (map kg ((k,l1) :: (k,l2) :: rest)).
    apply Permutation_map. exact Hperm. }
  assert (Hgl : Forall gStatic (map kg rest ++ [𝟘])).
  { apply Forall_app. split; [| constructor; [constructor | constructor]].
    apply Forall_forall. intros a Ha. apply elem_of_map_any in Ha.
    destruct Ha as ((k0, l0) & Hin & Heq). subst. unfold kg. simpl.
    apply kguard_gStatic. rewrite Forall_forall in Hrest. apply (Hrest (k0,l0) Hin). }
  eapply ax_trans;
    [apply (ax_merge_anywhere (build kl) k l1 l2 (map kg rest ++ [𝟘])
              (build_gStatic kl Hkl) H1 H2 Hs1 Hs2 Hgl Hpm) |].
  assert (Hkm : gStatic (kguard k (l1 ++ l2)))
    by (apply kguard_gStatic; apply Forall_app; split; assumption).
  assert (Hbr : gStatic (rebuild (map kg rest)))
    by (apply rebuild_gStatic; apply Forall_forall; intros a Ha;
        apply elem_of_map_any in Ha; destruct Ha as ((k0,l0) & Hin & Heq); subst;
        unfold kg; simpl; apply kguard_gStatic;
        rewrite Forall_forall in Hrest; apply (Hrest (k0,l0) Hin)).
  apply ax_cgr; [apply static_g; constructor; assumption |].
  apply cgr_fullchoice; [reflexivity | apply cgr_rebuild_snoc_nil].
Qed.

(** ** Iterating the merge

    Search and recursion, in the same shape as [canonicalize]
    ([VCCS_Canonical.v]) but on the association list, where the measure
    is simply [length] — each merge turns two entries into one — and the
    invariant carried through is [kmem]: which continuations sit under
    which key, as a *set*. That is all the caller needs, since
    [ax_ichoice_same_elems] makes multiplicity and order invisible. *)

Fixpoint kpick (k : act_key) (kl : list (act_key * list proc))
  : option (list proc * list (act_key * list proc)) :=
match kl with
| [] => None
| (k', l) :: kl' =>
    if decide (k' = k) then Some (l, kl')
    else match kpick k kl' with
         | Some (l0, r) => Some (l0, (k', l) :: r)
         | None => None
         end
end.

Lemma kpick_spec : forall k kl l r, kpick k kl = Some (l, r) ->
  Permutation kl ((k, l) :: r).
Proof.
  intros k kl. induction kl as [|(k', l') kl' IH]; intros l r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct (decide (k' = k)) as [He | He].
    + injection Heq as H1 H2. subst. reflexivity.
    + destruct (kpick k kl') as [(l0, r0)|] eqn:E; [| discriminate Heq].
      injection Heq as H1 H2. subst.
      etransitivity; [apply perm_skip; apply (IH l r0 eq_refl) | apply perm_swap].
Qed.

Fixpoint kfind_dup (kl : list (act_key * list proc))
  : option (act_key * (list proc) * (list proc) * (list (act_key * list proc))) :=
match kl with
| [] => None
| (k, l) :: kl' =>
    match kpick k kl' with
    | Some (l2, r) => Some (k, l, l2, r)
    | None => match kfind_dup kl' with
              | Some (k0, a, b, r) => Some (k0, a, b, (k, l) :: r)
              | None => None
              end
    end
end.

Lemma kfind_dup_spec : forall kl k l1 l2 r, kfind_dup kl = Some (k, l1, l2, r) ->
  Permutation kl ((k, l1) :: (k, l2) :: r).
Proof.
  induction kl as [|(k0, l0) kl' IH]; intros k l1 l2 r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct (kpick k0 kl') as [(l2', r')|] eqn:E.
    + injection Heq as H1 H2 H3 H4. subst.
      apply perm_skip. apply (kpick_spec k kl' l2 r E).
    + destruct (kfind_dup kl') as [(((k1, a), b), r1)|] eqn:E2; [| discriminate Heq].
      injection Heq as H1 H2 H3 H4. subst.
      etransitivity; [apply perm_skip; apply (IH k l1 l2 r1 eq_refl) |].
      etransitivity; [apply perm_swap |].
      apply perm_skip. apply perm_swap.
Qed.

Definition kmem (kl : list (act_key * list proc)) (k : act_key) (p : proc) : Prop :=
  exists l, (k, l) ∈ kl /\ p ∈ l.

Lemma kmem_perm : forall kl kl' k p, Permutation kl kl' -> (kmem kl k p <-> kmem kl' k p).
Proof.
  intros kl kl' k p Hp. unfold kmem. split; intros (l & Hin & Hpl); exists l;
    split; try assumption; [rewrite <- Hp | rewrite Hp]; assumption.
Qed.

Lemma kmem_merge : forall k l1 l2 r k0 p,
  kmem ((k, l1 ++ l2) :: r) k0 p <-> kmem ((k, l1) :: (k, l2) :: r) k0 p.
Proof.
  intros k l1 l2 r k0 p. unfold kmem. split.
  - intros (l & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as H1 H2. subst. apply elem_of_app in Hpl.
      destruct Hpl as [H | H].
      * exists l1. split; [apply elem_of_cons; left; reflexivity | exact H].
      * exists l2. split; [apply elem_of_cons; right; apply elem_of_cons; left; reflexivity
                          | exact H].
    + exists l. split; [apply elem_of_cons; right; apply elem_of_cons; right; exact Hin
                       | exact Hpl].
  - intros (l & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as H1 H2. subst.
      exists (l1 ++ l2). split; [apply elem_of_cons; left; reflexivity |].
      apply elem_of_app. left. exact Hpl.
    + apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
      * injection Heq as H1 H2. subst.
        exists (l1 ++ l2). split; [apply elem_of_cons; left; reflexivity |].
        apply elem_of_app. right. exact Hpl.
      * exists l. split; [apply elem_of_cons; right; exact Hin | exact Hpl].
Qed.

Theorem kcollapse : forall n kl, (length kl <= n)%nat ->
  Forall (fun p => Forall Static (snd p)) kl ->
  Forall (fun p => snd p <> []) kl ->
  exists kl',
    Forall (fun p => Forall Static (snd p)) kl'
    /\ Forall (fun p => snd p <> []) kl'
    /\ kfind_dup kl' = None
    /\ (forall k0 p0, kmem kl' k0 p0 <-> kmem kl k0 p0)
    /\ ax_pre (g (build kl)) (g (build kl')).
Proof.
  induction n as [|n IH]; intros kl Hlen Hst Hne.
  - exists kl. split; [exact Hst |]. split; [exact Hne |]. split.
    + destruct (kfind_dup kl) as [(((k,l1),l2),r)|] eqn:E; [| reflexivity].
      exfalso. pose proof (kfind_dup_spec kl k l1 l2 r E) as Hp.
      apply Permutation_length in Hp. simpl in Hp. lia.
    + split; [intros k0 p0; reflexivity | apply ax_refl].
  - destruct (kfind_dup kl) as [(((k,l1),l2),r)|] eqn:E.
    + pose proof (kfind_dup_spec kl k l1 l2 r E) as Hp.
      assert (Hst2 : Forall (fun p => Forall Static (snd p)) ((k,l1)::(k,l2)::r))
        by (eapply Permutation_Forall; [exact Hp | exact Hst]).
      assert (Hne2 : Forall (fun p => snd p <> []) ((k,l1)::(k,l2)::r))
        by (eapply Permutation_Forall; [exact Hp | exact Hne]).
      inversion Hst2 as [|? ? Ha1 Hst3]; subst.
      inversion Hst3 as [|? ? Ha2 Hstr]; subst.
      inversion Hne2 as [|? ? Hb1 Hne3]; subst.
      inversion Hne3 as [|? ? Hb2 Hner]; subst.
      simpl in Ha1, Ha2, Hb1, Hb2.
      assert (Hlen2 : (length ((k, l1 ++ l2) :: r) <= n)%nat).
      { apply Permutation_length in Hp. simpl in Hp. simpl. lia. }
      assert (Hst2' : Forall (fun p => Forall Static (snd p)) ((k, l1 ++ l2) :: r))
        by (constructor; [simpl; apply Forall_app; split; assumption | exact Hstr]).
      assert (Hne2' : Forall (fun p => snd p <> []) ((k, l1 ++ l2) :: r)).
      { constructor; [simpl; destruct l1; [contradiction | discriminate] | exact Hner]. }
      destruct (IH ((k, l1 ++ l2) :: r) Hlen2 Hst2' Hne2')
        as (kl' & A1 & A2 & A3 & A4 & A5).
      exists kl'. split; [exact A1 |]. split; [exact A2 |]. split; [exact A3 |]. split.
      * intros k0 p0. etransitivity; [apply A4 |].
        etransitivity; [apply kmem_merge |].
        symmetry. apply kmem_perm. exact Hp.
      * eapply ax_trans; [| exact A5].
        apply (ax_merge_klist kl k l1 l2 r Hst Hb1 Hb2 Ha1 Ha2 Hstr Hp).
    + exists kl. split; [exact Hst |]. split; [exact Hne |]. split; [exact E |].
      split; [intros k0 p0; reflexivity | apply ax_refl].
Qed.

(** Concatenating association lists is summing the built sums — the step
    the [⊕]-node needs after [ax_int_below_ext] has turned the two
    branches' internal choice into an external one. *)

Lemma cgr_build_app : forall kl1 kl2,
  g (build (kl1 ++ kl2)) ≡* g (build kl1 + build kl2).
Proof. intros kl1 kl2. unfold build. rewrite map_app. apply rebuild_app. Qed.

Lemma kmem_app : forall kl1 kl2 k p,
  kmem (kl1 ++ kl2) k p <-> (kmem kl1 k p \/ kmem kl2 k p).
Proof.
  intros kl1 kl2 k p. unfold kmem. split.
  - intros (l & Hin & Hpl). apply elem_of_app in Hin. destruct Hin as [H|H].
    + left. exists l. split; assumption.
    + right. exists l. split; assumption.
  - intros [(l & Hin & Hpl) | (l & Hin & Hpl)]; exists l; split; try assumption;
      apply elem_of_app; [left | right]; assumption.
Qed.

Lemma Forall_app_klist : forall (P : act_key * list proc -> Prop) kl1 kl2,
  Forall P kl1 -> Forall P kl2 -> Forall P (kl1 ++ kl2).
Proof. intros P kl1 kl2 H1 H2. apply Forall_app. split; assumption. Qed.

(** ** Restricting to an action set

    The induction that derives [⊢ g M ⊑ g (build …)] must carry the
    target's **action set** as a parameter. A first attempt without it —
    letting every node produce the sum of *all* its actions and applying
    [ax_convex] only at the very end — does not work: convexity needs
    its first branch to be a sub-sum of the middle term, i.e. the
    restriction of the big sum to the chosen leaf's action set, and
    [leaves_below] does not give [⊢ g M ⊑ g (that restriction)] (a
    leaf's own continuations are strictly poorer than [M]'s at the same
    action, so the leaf is *not* below the restriction).

    With the parameter, the [⊕]-node instantiates it as
    [S₁ := S ∩ keys kl₁] and [S₂ := keys kl₂]: then [S₁] still contains
    the chosen leaf's keys (put the leaf in the first branch), [S₂]
    admits any leaf of the second, and [S ⊆ S₁ ∪ S₂] — exactly the
    [S₁ ⊆ S ⊆ S₁ ∪ S₂] that [ax_convex] bridges. *)

Fixpoint krestrict (S : list act_key) (kl : list (act_key * list proc))
  : list (act_key * list proc) :=
match kl with
| [] => []
| (k, l) :: kl' => if decide (k ∈ S) then (k, l) :: krestrict S kl' else krestrict S kl'
end.

Lemma krestrict_Forall : forall (P : act_key * list proc -> Prop) S kl,
  Forall P kl -> Forall P (krestrict S kl).
Proof.
  intros P S kl. induction kl as [|(k,l) kl' IH]; intro H; simpl; [constructor |].
  inversion H as [|? ? Ha H']; subst.
  destruct (decide (k ∈ S)); [constructor; [exact Ha |] |]; apply IH; exact H'.
Qed.

Lemma kmem_krestrict : forall S kl k p,
  kmem (krestrict S kl) k p <-> (k ∈ S /\ kmem kl k p).
Proof.
  intros S kl k p. induction kl as [|(k0,l0) kl' IH]; simpl.
  - split; [intros (l & Hin & _); set_solver | intros (_ & (l & Hin & _)); set_solver].
  - destruct (decide (k0 ∈ S)) as [Hk | Hk]; unfold kmem in *; split.
    + intros (l & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
      * injection Heq as H1 H2. subst. split; [exact Hk |].
        exists l0. split; [apply elem_of_cons; left; reflexivity | exact Hpl].
      * destruct (proj1 IH (ex_intro _ l (conj Hin Hpl))) as (HkS & (l1 & Hin1 & Hp1)).
        split; [exact HkS |]. exists l1.
        split; [apply elem_of_cons; right; exact Hin1 | exact Hp1].
    + intros (HkS & (l & Hin & Hpl)). apply elem_of_cons in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as H1 H2. subst.
        exists l0. split; [apply elem_of_cons; left; reflexivity | exact Hpl].
      * destruct (proj2 IH (conj HkS (ex_intro _ l (conj Hin Hpl)))) as (l1 & Hin1 & Hp1).
        exists l1. split; [apply elem_of_cons; right; exact Hin1 | exact Hp1].
    + intro H. destruct (proj1 IH H) as (HkS & (l1 & Hin1 & Hp1)).
      split; [exact HkS |]. exists l1.
      split; [apply elem_of_cons; right; exact Hin1 | exact Hp1].
    + intros (HkS & (l & Hin & Hpl)). apply elem_of_cons in Hin.
      destruct Hin as [Heq | Hin].
      * injection Heq as H1 H2. subst. contradiction.
      * apply IH. split; [exact HkS |]. exists l. split; assumption.
Qed.

(** ** Sharing at an arbitrary summand — the ⊕-node's atom

    [ax_share_*] at a key occurring *somewhere* in each branch. Note the
    conclusion is a single **stable** sum: sharing collapses the internal
    choice, keeping the first branch's residue [r1] and pooling the two
    continuations at [k]. That is exactly the shape the ⊕-node needs —
    a target restricted to the first branch's ready set but already
    carrying both branches' continuations, which is what [ax_convex]
    then takes as its first component.

    Iterating over several shared keys is done by re-forming the choice
    with [ax_int_glb] between rounds (the second branch is unchanged, so
    it is always available); the measure is the number of keys not yet
    pooled. *)

Theorem ax_share_anywhere : forall B1 B2 k l1 l2 r1 r2,
  gStatic B1 -> gStatic B2 ->
  l1 <> [] -> l2 <> [] -> Forall Static l1 -> Forall Static l2 ->
  Forall gStatic r1 -> Forall gStatic r2 ->
  Permutation (summands B1) (kguard k l1 :: r1) ->
  Permutation (summands B2) (kguard k l2 :: r2) ->
  ax_pre (g ((𝛕 • (g B1)) + (𝛕 • (g B2))))
         (g (kguard k (l1 ++ l2) + rebuild r1)).
Proof.
  intros B1 B2 (c, [v|]) l1 l2 r1 r2 HB1 HB2 H1 H2 Hs1 Hs2 Hr1 Hr2 Hp1 Hp2;
    simpl in Hp1, Hp2 |- *.
  - assert (Hg1 : gStatic ((c ! v • (g (ichoice l1))) + rebuild r1))
      by (constructor; [constructor; apply static_g; apply ichoice_gStatic; exact Hs1
                       | apply rebuild_gStatic; exact Hr1]).
    assert (Hg2 : gStatic ((c ! v • (g (ichoice l2))) + rebuild r2))
      by (constructor; [constructor; apply static_g; apply ichoice_gStatic; exact Hs2
                       | apply rebuild_gStatic; exact Hr2]).
    eapply ax_trans;
      [apply ax_cgr with
         (q := g ((𝛕 • (g ((c ! v • (g (ichoice l1))) + rebuild r1)))
                  + (𝛕 • (g ((c ! v • (g (ichoice l2))) + rebuild r2)))));
         [apply static_g; constructor; constructor; apply static_g; assumption
         | apply cgr_fullchoice; apply cgr_tau; [apply pull_one; exact Hp1
                                                | apply pull_one; exact Hp2]] |].
    eapply ax_trans; [apply ax_share_out |].
    apply ax_choice_stable; [exact I | exact I |].
    apply ax_output. apply ax_ichoice_app_r; assumption.
  - assert (Hg1 : gStatic ((c ? (g (ichoice l1))) + rebuild r1))
      by (constructor; [constructor; apply static_g; apply ichoice_gStatic; exact Hs1
                       | apply rebuild_gStatic; exact Hr1]).
    assert (Hg2 : gStatic ((c ? (g (ichoice l2))) + rebuild r2))
      by (constructor; [constructor; apply static_g; apply ichoice_gStatic; exact Hs2
                       | apply rebuild_gStatic; exact Hr2]).
    eapply ax_trans;
      [apply ax_cgr with
         (q := g ((𝛕 • (g ((c ? (g (ichoice l1))) + rebuild r1)))
                  + (𝛕 • (g ((c ? (g (ichoice l2))) + rebuild r2)))));
         [apply static_g; constructor; constructor; apply static_g; assumption
         | apply cgr_fullchoice; apply cgr_tau; [apply pull_one; exact Hp1
                                                | apply pull_one; exact Hp2]] |].
    eapply ax_trans; [apply ax_share_in |].
    apply ax_choice_stable; [exact I | exact I |].
    apply ax_input. intro w. simpl. repeat rewrite subst_ichoice. rewrite map_app.
    apply (ax_ichoice_app_r (map (fun P => P^w) l1) (map (fun P => P^w) l2));
      [apply map_nonempty; exact H1 | apply map_nonempty; exact H2
       | apply Forall_Static_subst; exact Hs1 | apply Forall_Static_subst; exact Hs2].
Qed.

(** Sharing lifted to the association-list view, exactly as
    [ax_merge_klist] lifts merging. Same trailing-[𝟘] bookkeeping, same
    [cgr_rebuild_snoc_nil] fix.

    Note the **asymmetry**: the result is indexed by the *first* list's
    remainder [r1]. Sharing keeps the first branch's ready set and only
    enriches its continuation at [k] — which is what makes it usable to
    restrict a target while preserving both branches' behaviour. *)

Theorem ax_share_klist : forall kl1 kl2 k l1 l2 r1 r2,
  Forall (fun p => Forall Static (snd p)) kl1 ->
  Forall (fun p => Forall Static (snd p)) kl2 ->
  l1 <> [] -> l2 <> [] -> Forall Static l1 -> Forall Static l2 ->
  Forall (fun p => Forall Static (snd p)) r1 ->
  Forall (fun p => Forall Static (snd p)) r2 ->
  Permutation kl1 ((k, l1) :: r1) -> Permutation kl2 ((k, l2) :: r2) ->
  ax_pre (g ((𝛕 • (g (build kl1))) + (𝛕 • (g (build kl2)))))
         (g (build ((k, l1 ++ l2) :: r1))).
Proof.
  intros kl1 kl2 k l1 l2 r1 r2 Hk1 Hk2 H1 H2 Hs1 Hs2 Hr1 Hr2 Hp1 Hp2.
  set (kg := fun p : act_key * list proc => kguard (fst p) (snd p)).
  assert (Hgs : forall rr, Forall (fun p => Forall Static (snd p)) rr ->
                  Forall gStatic (map kg rr ++ [𝟘])).
  { intros rr Hrr. apply Forall_app.
    split; [| constructor; [constructor | constructor]].
    apply Forall_forall. intros a Ha. apply elem_of_map_any in Ha.
    destruct Ha as ((k0, l0) & Hin & Heq). subst. unfold kg. simpl.
    apply kguard_gStatic. rewrite Forall_forall in Hrr. apply (Hrr (k0,l0) Hin). }
  assert (Hpm1 : Permutation (summands (build kl1))
                   (kguard k l1 :: (map kg r1 ++ [𝟘]))).
  { rewrite summands_build.
    change (kguard k l1 :: (map kg r1 ++ [𝟘])) with ((kg (k, l1) :: map kg r1) ++ [𝟘]).
    apply Permutation_app_tail.
    change (kg (k,l1) :: map kg r1) with (map kg ((k,l1) :: r1)).
    apply Permutation_map. exact Hp1. }
  assert (Hpm2 : Permutation (summands (build kl2))
                   (kguard k l2 :: (map kg r2 ++ [𝟘]))).
  { rewrite summands_build.
    change (kguard k l2 :: (map kg r2 ++ [𝟘])) with ((kg (k, l2) :: map kg r2) ++ [𝟘]).
    apply Permutation_app_tail.
    change (kg (k,l2) :: map kg r2) with (map kg ((k,l2) :: r2)).
    apply Permutation_map. exact Hp2. }
  eapply ax_trans;
    [apply (ax_share_anywhere (build kl1) (build kl2) k l1 l2
              (map kg r1 ++ [𝟘]) (map kg r2 ++ [𝟘])
              (build_gStatic kl1 Hk1) (build_gStatic kl2 Hk2)
              H1 H2 Hs1 Hs2 (Hgs r1 Hr1) (Hgs r2 Hr2) Hpm1 Hpm2) |].
  assert (Hkm : gStatic (kguard k (l1 ++ l2)))
    by (apply kguard_gStatic; apply Forall_app; split; assumption).
  assert (Hbr : gStatic (rebuild (map kg r1)))
    by (apply rebuild_gStatic; apply Forall_forall; intros a Ha;
        apply elem_of_map_any in Ha; destruct Ha as ((k0,l0) & Hin & Heq); subst;
        unfold kg; simpl; apply kguard_gStatic;
        rewrite Forall_forall in Hr1; apply (Hr1 (k0,l0) Hin)).
  apply ax_cgr; [apply static_g; constructor; assumption |].
  apply cgr_fullchoice; [reflexivity | apply cgr_rebuild_snoc_nil].
Qed.

(** ** One round of the sharing iteration, with its invariants

    Pooling at one key, packaged with everything the iteration has to
    carry: the key set is unchanged, the first list's members survive,
    the second list's members at that key are added, and nothing is
    invented. The derivation step is [ax_int_glb] (to re-form the
    internal choice from the two facts about [q]) followed by
    [ax_share_klist].

    Keeping the *second* list fixed across rounds is what makes the
    iteration's measure work: pooling does not shrink [kl2], and
    [⊢ q ⊑ build (kl2 minus k)] is not available, so the recursion must
    shrink a separate worklist instead. *)

Definition khas (kl : list (act_key * list proc)) (k : act_key) : Prop :=
  exists l, (k, l) ∈ kl.

Lemma khas_perm : forall kl kl' k, Permutation kl kl' -> (khas kl k <-> khas kl' k).
Proof.
  intros kl kl' k Hp. unfold khas. split; intros (l & Hin); exists l;
    [rewrite <- Hp | rewrite Hp]; assumption.
Qed.

Lemma kshare_step : forall kl1 kl2 k l1 l2 r1 r2 q,
  Forall (fun p => Forall Static (snd p)) kl1 ->
  Forall (fun p => Forall Static (snd p)) kl2 ->
  l1 <> [] -> l2 <> [] -> Forall Static l1 -> Forall Static l2 ->
  Forall (fun p => Forall Static (snd p)) r1 ->
  Forall (fun p => Forall Static (snd p)) r2 ->
  Forall (fun p => snd p <> []) r1 ->
  Permutation kl1 ((k, l1) :: r1) -> Permutation kl2 ((k, l2) :: r2) ->
  ax_pre q (g (build kl1)) -> ax_pre q (g (build kl2)) ->
  Forall (fun p => Forall Static (snd p)) ((k, l1 ++ l2) :: r1)
  /\ Forall (fun p => snd p <> []) ((k, l1 ++ l2) :: r1)
  /\ (forall k0, khas ((k, l1 ++ l2) :: r1) k0 <-> khas kl1 k0)
  /\ (forall k0 p0, kmem kl1 k0 p0 -> kmem ((k, l1 ++ l2) :: r1) k0 p0)
  /\ (forall p0, p0 ∈ l2 -> kmem ((k, l1 ++ l2) :: r1) k p0)
  /\ (forall k0 p0, kmem ((k, l1 ++ l2) :: r1) k0 p0 -> kmem kl1 k0 p0 \/ kmem kl2 k0 p0)
  /\ ax_pre q (g (build ((k, l1 ++ l2) :: r1))).
Proof.
  intros kl1 kl2 k l1 l2 r1 r2 q Hk1 Hk2 H1 H2 Hs1 Hs2 Hr1 Hr2 Hn1 Hp1 Hp2 Hq1 Hq2.
  assert (Hst' : Forall (fun p => Forall Static (snd p)) ((k, l1 ++ l2) :: r1))
    by (constructor; [simpl; apply Forall_app; split; assumption | exact Hr1]).
  assert (Hne' : Forall (fun p => snd p <> []) ((k, l1 ++ l2) :: r1))
    by (constructor; [simpl; destruct l1; [contradiction | discriminate] | exact Hn1]).
  split; [exact Hst' |]. split; [exact Hne' |]. split.
  { intro k0. split.
    - intro H. rewrite (khas_perm kl1 _ k0 Hp1). unfold khas in *.
      destruct H as (l & Hin). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
      + injection Heq as Ha Hb. subst. exists l1. apply elem_of_cons. left. reflexivity.
      + exists l. apply elem_of_cons. right. exact Hin.
    - intro H. rewrite (khas_perm kl1 _ k0 Hp1) in H. unfold khas in *.
      destruct H as (l & Hin). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
      + injection Heq as Ha Hb. subst. exists (l1 ++ l2).
        apply elem_of_cons. left. reflexivity.
      + exists l. apply elem_of_cons. right. exact Hin. }
  split.
  { intros k0 p0 H. rewrite (kmem_perm kl1 _ k0 p0 Hp1) in H.
    destruct H as (l & Hin & Hpl).
    apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    - injection Heq as Ha Hb. subst. exists (l1 ++ l2).
      split; [apply elem_of_cons; left; reflexivity | apply elem_of_app; left; exact Hpl].
    - exists l. split; [apply elem_of_cons; right; exact Hin | exact Hpl]. }
  split.
  { intros p0 Hp0. exists (l1 ++ l2).
    split; [apply elem_of_cons; left; reflexivity | apply elem_of_app; right; exact Hp0]. }
  split.
  { intros k0 p0 (l & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    - injection Heq as Ha Hb. subst. apply elem_of_app in Hpl. destruct Hpl as [H | H].
      + left. rewrite (kmem_perm kl1 _ k p0 Hp1). exists l1.
        split; [apply elem_of_cons; left; reflexivity | exact H].
      + right. rewrite (kmem_perm kl2 _ k p0 Hp2). exists l2.
        split; [apply elem_of_cons; left; reflexivity | exact H].
    - left. rewrite (kmem_perm kl1 _ k0 p0 Hp1). exists l.
      split; [apply elem_of_cons; right; exact Hin | exact Hpl]. }
  eapply ax_trans; [apply ax_int_glb; [exact Hq1 | exact Hq2] |].
  apply (ax_share_klist kl1 kl2 k l1 l2 r1 r2); assumption.
Qed.

(** ** The sharing iteration

    Pool every key the two branches share, one round at a time. The
    recursion is on a **worklist** of `kl2`-entries rather than on `kl2`
    itself: pooling leaves `kl2` untouched (it must, since
    [⊢ q ⊑ build kl2] has to stay available to re-form the internal
    choice each round), so the measure has to live somewhere else.

    The result keeps the first list's key set exactly, contains
    everything either list had at those keys, and invents nothing. *)

Lemma kpick_none : forall k kl, kpick k kl = None -> ~ khas kl k.
Proof.
  intros k kl. induction kl as [|(k', l') kl' IH]; intro Heq; simpl in Heq.
  - intros (l & Hin). set_solver.
  - destruct (decide (k' = k)) as [He | He]; [discriminate Heq |].
    destruct (kpick k kl') as [(l0, r0)|] eqn:E; [discriminate Heq |].
    intros (l & Hin). apply elem_of_cons in Hin. destruct Hin as [Hc | Hin].
    + injection Hc as Ha Hb. subst. contradiction.
    + apply (IH eq_refl). exists l. exact Hin.
Qed.

Theorem kshare_iter : forall (todo kl1 kl2 : list (act_key * list proc)) (q : proc),
  Forall (fun p => Forall Static (snd p)) kl1 ->
  Forall (fun p => snd p <> []) kl1 ->
  Forall (fun p => Forall Static (snd p)) kl2 ->
  Forall (fun p => snd p <> []) kl2 ->
  (forall e, e ∈ todo -> exists r, Permutation kl2 (e :: r)) ->
  ax_pre q (g (build kl1)) -> ax_pre q (g (build kl2)) ->
  exists kl,
    Forall (fun p => Forall Static (snd p)) kl
    /\ Forall (fun p => snd p <> []) kl
    /\ (forall k0, khas kl k0 <-> khas kl1 k0)
    /\ (forall k0 p0, kmem kl1 k0 p0 -> kmem kl k0 p0)
    /\ (forall e, e ∈ todo -> khas kl1 (fst e) ->
          forall p0, p0 ∈ snd e -> kmem kl (fst e) p0)
    /\ (forall k0 p0, kmem kl k0 p0 -> kmem kl1 k0 p0 \/ kmem kl2 k0 p0)
    /\ ax_pre q (g (build kl)).
Proof.
  induction todo as [|e todo IH]; intros kl1 kl2 q Hst1 Hne1 Hst2 Hne2 Htodo Hq1 Hq2.
  - exists kl1. split; [exact Hst1 |]. split; [exact Hne1 |].
    split; [intro k0; reflexivity |].
    split; [intros k0 p0 H; exact H |].
    split; [intros e He; set_solver |].
    split; [intros k0 p0 H; left; exact H | exact Hq1].
  - destruct e as (k, l2).
    destruct (Htodo (k, l2) ltac:(apply elem_of_cons; left; reflexivity)) as (r2 & Hp2).
    assert (Htodo' : forall e, e ∈ todo -> exists r, Permutation kl2 (e :: r))
      by (intros e0 He0; apply Htodo; apply elem_of_cons; right; exact He0).
    destruct (kpick k kl1) as [(l1, r1)|] eqn:E.
    + pose proof (kpick_spec k kl1 l1 r1 E) as Hp1.
      assert (Ha1 : Forall (fun p => Forall Static (snd p)) ((k,l1) :: r1))
        by (eapply Permutation_Forall; [exact Hp1 | exact Hst1]).
      assert (Hb1 : Forall (fun p => snd p <> []) ((k,l1) :: r1))
        by (eapply Permutation_Forall; [exact Hp1 | exact Hne1]).
      assert (Ha2 : Forall (fun p => Forall Static (snd p)) ((k,l2) :: r2))
        by (eapply Permutation_Forall; [exact Hp2 | exact Hst2]).
      assert (Hb2 : Forall (fun p => snd p <> []) ((k,l2) :: r2))
        by (eapply Permutation_Forall; [exact Hp2 | exact Hne2]).
      inversion Ha1 as [|? ? Hl1 Hr1]; subst.
      inversion Hb1 as [|? ? Hn1 Hnr1]; subst.
      inversion Ha2 as [|? ? Hl2 Hr2]; subst.
      inversion Hb2 as [|? ? Hn2 Hnr2]; subst.
      simpl in Hl1, Hn1, Hl2, Hn2.
      destruct (kshare_step kl1 kl2 k l1 l2 r1 r2 q Hst1 Hst2 Hn1 Hn2 Hl1 Hl2
                  Hr1 Hr2 Hnr1 Hp1 Hp2 Hq1 Hq2)
        as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
      destruct (IH ((k, l1 ++ l2) :: r1) kl2 q A1 A2 Hst2 Hne2 Htodo' A7 Hq2)
        as (kl & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      exists kl. split; [exact B1 |]. split; [exact B2 |].
      split; [intro k0; etransitivity; [apply B3 | apply A3] |].
      split; [intros k0 p0 H; apply B4; apply A4; exact H |].
      split.
      { intros e0 He0 Hk0 p0 Hp0. apply elem_of_cons in He0.
        destruct He0 as [Heq | He0].
        - subst. simpl in *. apply B4. apply A5. exact Hp0.
        - apply B5; [exact He0 | apply A3; exact Hk0 | exact Hp0]. }
      split; [| exact B7].
      intros k0 p0 H. destruct (B6 k0 p0 H) as [H' | H']; [| right; exact H'].
      apply A6. exact H'.
    + destruct (IH kl1 kl2 q Hst1 Hne1 Hst2 Hne2 Htodo' Hq1 Hq2)
        as (kl & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      exists kl. split; [exact B1 |]. split; [exact B2 |]. split; [exact B3 |].
      split; [exact B4 |].
      split; [| split; [exact B6 | exact B7]].
      intros e0 He0 Hk0 p0 Hp0. apply elem_of_cons in He0.
      destruct He0 as [Heq | He0].
      * subst. simpl in Hk0. exfalso. apply (kpick_none k kl1 E). exact Hk0.
      * apply B5; assumption.
Qed.

(** ** Reading a duplicate-free association list

    On a list with no repeated key, [kmem] at the head's key is just
    membership in the head's own continuation list, and everything at
    another key lives in the tail. These are what the alignment argument
    (two duplicate-free lists with the same keys and the same [kmem] are
    [⊢]-equal) reads its per-key facts from.

    Note [injection] on `(k, l0) = (k, l)` yields **one** equation, not
    two, when the first components are syntactically identical — supply
    a single introduction pattern there. *)

Lemma kpick_some : forall k kl, khas kl k -> exists l r, kpick k kl = Some (l, r).
Proof.
  intros k kl H. destruct (kpick k kl) as [(l,r)|] eqn:E.
  - exists l, r. reflexivity.
  - exfalso. apply (kpick_none k kl E). exact H.
Qed.

Lemma kfind_dup_cons_none : forall k l r,
  kfind_dup ((k, l) :: r) = None -> kpick k r = None /\ kfind_dup r = None.
Proof.
  intros k l r H. simpl in H.
  destruct (kpick k r) as [(l2,r2)|] eqn:E; [discriminate H |].
  destruct (kfind_dup r) as [(((k1,a),b),r1)|] eqn:E2; [discriminate H |].
  split; reflexivity.
Qed.

Lemma kmem_head_dupfree : forall k l r p,
  kpick k r = None -> (kmem ((k, l) :: r) k p <-> p ∈ l).
Proof.
  intros k l r p Hnone. split.
  - intros (l0 & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as Hb. subst. exact Hpl.
    + exfalso. apply (kpick_none k r Hnone). exists l0. exact Hin.
  - intro H. exists l. split; [apply elem_of_cons; left; reflexivity | exact H].
Qed.

Lemma kmem_tail_dupfree : forall k l r k0 p,
  kpick k r = None -> k0 <> k ->
  (kmem ((k, l) :: r) k0 p <-> kmem r k0 p).
Proof.
  intros k l r k0 p Hnone Hne. split.
  - intros (l0 & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as Ha Hb. subst. contradiction.
    + exists l0. split; assumption.
  - intros (l0 & Hin & Hpl). exists l0.
    split; [apply elem_of_cons; right; exact Hin | exact Hpl].
Qed.

Lemma khas_tail_dupfree : forall k l r k0,
  kpick k r = None -> k0 <> k -> (khas ((k, l) :: r) k0 <-> khas r k0).
Proof.
  intros k l r k0 Hnone Hne. split.
  - intros (l0 & Hin). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as Ha Hb. subst. contradiction.
    + exists l0. exact Hin.
  - intros (l0 & Hin). exists l0. apply elem_of_cons. right. exact Hin.
Qed.

(** Duplicate-freeness survives [kpick]: removing the (unique) entry at
    a key leaves a list that is still duplicate-free and no longer
    mentions that key. This is what lets the alignment induction peel
    one key at a time off *both* lists and keep its hypotheses. *)

Lemma kpick_none_conv : forall k kl, ~ khas kl k -> kpick k kl = None.
Proof.
  intros k kl. induction kl as [|(k',l') kl' IH]; intro H; simpl; [reflexivity |].
  destruct (decide (k' = k)) as [He | He].
  - exfalso. subst. apply H. exists l'. apply elem_of_cons. left. reflexivity.
  - rewrite IH; [reflexivity |]. intros (l0 & Hin). apply H.
    exists l0. apply elem_of_cons. right. exact Hin.
Qed.

Lemma kpick_sub : forall k kl l r x, kpick k kl = Some (l, r) -> khas r x -> khas kl x.
Proof.
  intros k kl l r x Heq Hx.
  pose proof (kpick_spec k kl l r Heq) as Hp.
  rewrite (khas_perm kl _ x Hp). destruct Hx as (l0 & Hin).
  exists l0. apply elem_of_cons. right. exact Hin.
Qed.

Lemma kfind_dup_pick : forall k kl l r,
  kfind_dup kl = None -> kpick k kl = Some (l, r) ->
  kfind_dup r = None /\ kpick k r = None.
Proof.
  intros k kl. induction kl as [|(k0,l0) t IH]; intros l r Hd Heq; simpl in Heq.
  - discriminate Heq.
  - destruct (kfind_dup_cons_none k0 l0 t Hd) as (Hn0 & Hdt).
    destruct (decide (k0 = k)) as [He | He].
    + injection Heq as Ha Hb. subst. split; [exact Hdt | exact Hn0].
    + destruct (kpick k t) as [(l1,r1)|] eqn:E; [| discriminate Heq].
      injection Heq as Ha Hb. subst.
      destruct (IH l r1 Hdt eq_refl) as (Hdr1 & Hnr1).
      split.
      * simpl. rewrite kpick_none_conv; [rewrite Hdr1; reflexivity |].
        intro Hx. apply (kpick_none k0 t Hn0). eapply kpick_sub; [exact E | exact Hx].
      * simpl. destruct (decide (k0 = k)); [contradiction |].
        rewrite Hnr1. reflexivity.
Qed.

(** A guard whose continuation list is replaced by an element-equal one.
    The input case is where substitution has to commute past the
    [ichoice] again, and the element-equality is transported through the
    [map] pointwise. *)

Lemma ax_kguard_same_elems : forall k l l', l <> [] -> l' <> [] ->
  Forall Static l -> Forall Static l' -> (forall p, p ∈ l <-> p ∈ l') ->
  ax_pre (g (kguard k l)) (g (kguard k l')).
Proof.
  intros (c,[v|]) l l' H1 H2 Hs1 Hs2 Hiff; simpl.
  - apply ax_output. apply ax_ichoice_same_elems; assumption.
  - apply ax_input. intro w. simpl. repeat rewrite subst_ichoice.
    apply ax_ichoice_same_elems.
    + apply map_nonempty; exact H1.
    + apply map_nonempty; exact H2.
    + apply Forall_Static_subst; exact Hs1.
    + apply Forall_Static_subst; exact Hs2.
    + intro p. repeat rewrite elem_of_map_any. split.
      * intros (q & Hq & Heq). exists q. split; [apply Hiff; exact Hq | exact Heq].
      * intros (q & Hq & Heq). exists q. split; [apply Hiff; exact Hq | exact Heq].
Qed.

(** ** Alignment: same keys and same [kmem] ⟹ [⊢]-equal

    Two duplicate-free association lists that agree on which keys they
    carry and on which continuations sit under each key build
    [⊢]-comparable sums — regardless of order or multiplicity inside the
    continuation lists.

    This is what reconciles the two ways the ⊕-node produces its
    restricted target: [kshare_iter] returns a list that is [kmem]-equal
    to, but not syntactically, the restriction of the collapsed list
    that [ax_convex_anywhere] needs as a sub-sum.

    The induction peels the head key off *both* lists — [kpick] finds it
    on the right, [kfind_dup_pick] keeps both tails duplicate-free — then
    rewrites the head with [ax_kguard_same_elems] and the tail with the
    induction hypothesis, commuting in between exactly as
    [ax_match_lists] does. *)

Lemma kguard_gStable : forall k l, gStable (kguard k l).
Proof. intros (c,[v|]) l; exact I. Qed.

Theorem ax_build_align : forall n kl kl', (length kl <= n)%nat ->
  Forall (fun p => Forall Static (snd p)) kl ->
  Forall (fun p => snd p <> []) kl ->
  Forall (fun p => Forall Static (snd p)) kl' ->
  Forall (fun p => snd p <> []) kl' ->
  kfind_dup kl = None -> kfind_dup kl' = None ->
  (forall k, khas kl k <-> khas kl' k) ->
  (forall k p, kmem kl k p <-> kmem kl' k p) ->
  ax_pre (g (build kl)) (g (build kl')).
Proof.
  induction n as [|n IH]; intros kl kl' Hlen Hs Hn Hs' Hn' Hd Hd' Hkeys Hmem.
  - destruct kl as [|(k,l) r]; [| simpl in Hlen; lia].
    destruct kl' as [|(k',l') r']; [apply ax_refl |].
    exfalso.
    assert (Hk : khas ((k',l')::r') k')
      by (exists l'; apply elem_of_cons; left; reflexivity).
    apply Hkeys in Hk. destruct Hk as (l0 & Hin). set_solver.
  - destruct kl as [|(k,l) r].
    + destruct kl' as [|(k',l') r']; [apply ax_refl |].
      exfalso.
      assert (Hk : khas ((k',l')::r') k')
        by (exists l'; apply elem_of_cons; left; reflexivity).
      apply Hkeys in Hk. destruct Hk as (l0 & Hin). set_solver.
    + destruct (kfind_dup_cons_none k l r Hd) as (Hnr & Hdr).
      assert (Hk : khas ((k,l)::r) k)
        by (exists l; apply elem_of_cons; left; reflexivity).
      apply Hkeys in Hk.
      destruct (kpick_some k kl' Hk) as (l' & r' & E).
      pose proof (kpick_spec k kl' l' r' E) as Hp'.
      destruct (kfind_dup_pick k kl' l' r' Hd' E) as (Hdr' & Hnr').
      inversion Hs as [|? ? Hl Hr]; subst.
      inversion Hn as [|? ? Hnl Hnrr]; subst. simpl in Hl, Hnl.
      assert (Hs2 : Forall (fun p => Forall Static (snd p)) ((k,l')::r'))
        by (eapply Permutation_Forall; [exact Hp' | exact Hs']).
      assert (Hn2 : Forall (fun p => snd p <> []) ((k,l')::r'))
        by (eapply Permutation_Forall; [exact Hp' | exact Hn']).
      inversion Hs2 as [|? ? Hl' Hr']; subst.
      inversion Hn2 as [|? ? Hnl' Hnr2]; subst. simpl in Hl', Hnl'.
      assert (Helem : forall p, p ∈ l <-> p ∈ l').
      { intro p. rewrite <- (kmem_head_dupfree k l r p Hnr).
        rewrite (Hmem k p). rewrite (kmem_perm kl' _ k p Hp').
        apply kmem_head_dupfree. exact Hnr'. }
      assert (Hkeys2 : forall k0, khas r k0 <-> khas r' k0).
      { intro k0. destruct (decide (k0 = k)) as [He|He].
        - subst. split; intro H; exfalso;
            [apply (kpick_none k r Hnr) | apply (kpick_none k r' Hnr')]; exact H.
        - rewrite <- (khas_tail_dupfree k l r k0 Hnr He).
          rewrite (Hkeys k0). rewrite (khas_perm kl' _ k0 Hp').
          apply khas_tail_dupfree; assumption. }
      assert (Hmem2 : forall k0 p, kmem r k0 p <-> kmem r' k0 p).
      { intros k0 p. destruct (decide (k0 = k)) as [He|He].
        - subst. split; intros (l0 & Hin & _); exfalso;
            [apply (kpick_none k r Hnr) | apply (kpick_none k r' Hnr')];
            exists l0; exact Hin.
        - rewrite <- (kmem_tail_dupfree k l r k0 p Hnr He).
          rewrite (Hmem k0 p). rewrite (kmem_perm kl' _ k0 p Hp').
          apply kmem_tail_dupfree; assumption. }
      assert (Hlen2 : (length r <= n)%nat) by (simpl in Hlen; lia).
      pose proof (IH r r' Hlen2 Hr Hnrr Hr' Hnr2 Hdr Hdr' Hkeys2 Hmem2) as HIH.
      assert (Hgk' : gStatic (kguard k l')) by (apply kguard_gStatic; exact Hl').
      assert (Hbr : gStatic (build r)) by (apply build_gStatic; exact Hr).
      assert (Hbr' : gStatic (build r')) by (apply build_gStatic; exact Hr').
      eapply ax_trans;
        [apply (ax_choice_stable (kguard k l) (kguard k l') (build r));
           [apply kguard_gStable | apply kguard_gStable |
            apply ax_kguard_same_elems; assumption] |].
      eapply ax_trans;
        [apply ax_cgr with (q := g (build r + kguard k l'));
           [apply static_g; constructor; assumption | apply cgr_choice_com] |].
      eapply ax_trans;
        [apply (ax_choice_stable (build r) (build r') (kguard k l'));
           [apply build_gStable | apply build_gStable | exact HIH] |].
      eapply ax_trans;
        [apply ax_cgr with (q := g (kguard k l' + build r'));
           [apply static_g; constructor; assumption | apply cgr_choice_com] |].
      apply ax_cgr; [apply static_g; apply build_gStatic; exact Hs' |].
      change (kguard k l' + build r') with (build ((k, l') :: r')).
      unfold build. apply rebuild_perm. apply Permutation_map. symmetry. exact Hp'.
Qed.

(** The restriction/complement split. This is what supplies
    [ax_convex_anywhere]'s permutation hypothesis: the restricted list
    really is a sub-list of the full one, so the built sums stand in the
    sub-sum relation the convexity rule requires. *)

Fixpoint kexclude (S : list act_key) (kl : list (act_key * list proc))
  : list (act_key * list proc) :=
match kl with
| [] => []
| (k, l) :: kl' => if decide (k ∈ S) then kexclude S kl' else (k, l) :: kexclude S kl'
end.

Lemma krestrict_split : forall S kl,
  Permutation kl (krestrict S kl ++ kexclude S kl).
Proof.
  intros S kl. induction kl as [|(k,l) kl' IH]; simpl; [reflexivity |].
  destruct (decide (k ∈ S)) as [He | He]; simpl.
  - apply perm_skip. exact IH.
  - etransitivity; [apply perm_skip; exact IH | apply Permutation_middle].
Qed.

Lemma kexclude_Forall : forall (P : act_key * list proc -> Prop) S kl,
  Forall P kl -> Forall P (kexclude S kl).
Proof.
  intros P S kl. induction kl as [|(k,l) kl' IH]; intro H; simpl; [constructor |].
  inversion H as [|? ? Ha H']; subst.
  destruct (decide (k ∈ S)); [| constructor; [exact Ha |]]; apply IH; exact H'.
Qed.

(* ------------------------------------------------------------------ *)
(* The main induction's leaf case.                                     *)
(*                                                                     *)
(* [conts_at_g] is the *stable-sum* reading of [conts_at]: it collects  *)
(* a guarded sum's own input/output continuations directly, without     *)
(* going through [leaves].  For a stable [A] the two agree              *)
(* ([conts_at_stable]), and [conts_at_g] is the one that distributes    *)
(* over [summands] ([conts_at_g_summands]) — which is what connects a   *)
(* leaf's continuations to the association list [klist] builds from its *)
(* summands.                                                           *)

Definition conts_at_g (A : gproc) (k : act_key) : list proc :=
match k with
| (c, None) => in_conts_g A c
| (c, Some v) => out_conts_g A c v
end.

Lemma conts_at_g_app : forall A1 A2 k,
  conts_at_g (A1 + A2) k = conts_at_g A1 k ++ conts_at_g A2 k.
Proof. intros A1 A2 (c,[v|]); reflexivity. Qed.

Lemma exists_in_singleton : forall (A : gproc) k p,
  (exists a, a ∈ [A] /\ p ∈ conts_at_g a k) <-> p ∈ conts_at_g A k.
Proof.
  intros A k p. split.
  - intros (a & Ha & Hp). assert (a = A) by set_solver. subst. exact Hp.
  - intro H. exists A. split; [set_solver | exact H].
Qed.

Lemma conts_at_g_summands : forall A k p,
  p ∈ conts_at_g A k <-> exists a, a ∈ summands A /\ p ∈ conts_at_g a k.
Proof.
  intro A. induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IH1 A2 IH2 ]; intros k p;
    try (simpl summands; symmetry; apply exists_in_singleton).
  rewrite conts_at_g_app. simpl summands. split.
  - intro H. apply elem_of_app in H. destruct H as [H|H].
    + destruct (proj1 (IH1 k p) H) as (a & Ha & Hp).
      exists a. split; [apply elem_of_app; left; exact Ha | exact Hp].
    + destruct (proj1 (IH2 k p) H) as (a & Ha & Hp).
      exists a. split; [apply elem_of_app; right; exact Ha | exact Hp].
  - intros (a & Ha & Hp). apply elem_of_app in Ha. apply elem_of_app.
    destruct Ha as [Ha|Ha].
    + left. apply IH1. exists a. split; assumption.
    + right. apply IH2. exists a. split; assumption.
Qed.

(* [klist] skips a summand that is itself a sum, so this needs the      *)
(* leaf hypothesis — which [summands_leaves] supplies at every call.    *)
Lemma kmem_klist : forall l, Forall (fun a => summands a = [a]) l ->
  forall k p, kmem (klist l) k p <-> exists a, a ∈ l /\ p ∈ conts_at_g a k.
Proof.
  induction l as [|a l IH]; intros Hl k p; simpl.
  - split; [intros (l0 & Hin & _); set_solver | intros (b & Hb & _); set_solver].
  - assert (Hleaf := Forall_inv Hl). assert (Hl' := Forall_inv_tail Hl).
    destruct a as [ | | c P | c v P | P | A1 A2 ]; unfold kmem in *.
    + split.
      * intro H. apply (IH Hl') in H. destruct H as (b & Hb & Hp).
        exists b. split; [apply elem_of_cons; right; exact Hb | exact Hp].
      * intros (b & Hb & Hp). apply elem_of_cons in Hb. destruct Hb as [Heq | Hb].
        { subst. destruct k as (c,[v|]); simpl in Hp; set_solver. }
        { apply (IH Hl'). exists b. split; assumption. }
    + split.
      * intro H. apply (IH Hl') in H. destruct H as (b & Hb & Hp).
        exists b. split; [apply elem_of_cons; right; exact Hb | exact Hp].
      * intros (b & Hb & Hp). apply elem_of_cons in Hb. destruct Hb as [Heq | Hb].
        { subst. destruct k as (c,[v|]); simpl in Hp; set_solver. }
        { apply (IH Hl'). exists b. split; assumption. }
    + split.
      * intros (l0 & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
        { injection Heq as Ha Hb. subst. exists (c ? P).
          split; [apply elem_of_cons; left; reflexivity |].
          simpl. destruct (decide (c = c)); [exact Hpl | contradiction]. }
        { destruct (proj1 (IH Hl' k p) (ex_intro _ l0 (conj Hin Hpl))) as (b & Hb & Hp).
          exists b. split; [apply elem_of_cons; right; exact Hb | exact Hp]. }
      * intros (b & Hb & Hp). apply elem_of_cons in Hb. destruct Hb as [Heq | Hb].
        { subst. destruct k as (c0,[v0|]); simpl in Hp; [set_solver |].
          destruct (decide (c = c0)) as [He|He]; [| set_solver].
          subst. exists [P]. split; [apply elem_of_cons; left; reflexivity | exact Hp]. }
        { destruct (proj2 (IH Hl' k p) (ex_intro _ b (conj Hb Hp))) as (l0 & Hin & Hpl).
          exists l0. split; [apply elem_of_cons; right; exact Hin | exact Hpl]. }
    + split.
      * intros (l0 & Hin & Hpl). apply elem_of_cons in Hin. destruct Hin as [Heq | Hin].
        { injection Heq as Ha Hb. subst. exists (c ! v • P).
          split; [apply elem_of_cons; left; reflexivity |].
          simpl. destruct (decide (c = c)); [| contradiction].
          destruct (decide (v = v)); [exact Hpl | contradiction]. }
        { destruct (proj1 (IH Hl' k p) (ex_intro _ l0 (conj Hin Hpl))) as (b & Hb & Hp).
          exists b. split; [apply elem_of_cons; right; exact Hb | exact Hp]. }
      * intros (b & Hb & Hp). apply elem_of_cons in Hb. destruct Hb as [Heq | Hb].
        { subst. destruct k as (c0,[v0|]); simpl in Hp; [| set_solver].
          destruct (decide (c = c0)) as [He|He]; [| set_solver].
          destruct (decide (v = v0)) as [Hv|Hv]; [| set_solver].
          subst. exists [P]. split; [apply elem_of_cons; left; reflexivity | exact Hp]. }
        { destruct (proj2 (IH Hl' k p) (ex_intro _ b (conj Hb Hp))) as (l0 & Hin & Hpl).
          exists l0. split; [apply elem_of_cons; right; exact Hin | exact Hpl]. }
    + split.
      * intro H. apply (IH Hl') in H. destruct H as (b & Hb & Hp).
        exists b. split; [apply elem_of_cons; right; exact Hb | exact Hp].
      * intros (b & Hb & Hp). apply elem_of_cons in Hb. destruct Hb as [Heq | Hb].
        { subst. destruct k as (c,[v|]); simpl in Hp; set_solver. }
        { apply (IH Hl'). exists b. split; assumption. }
    + exfalso. simpl in Hleaf.
      assert (H1 := summands_nonempty A1). assert (H2 := summands_nonempty A2).
      destruct (summands A1) as [|x1 l1]; [contradiction |].
      destruct (summands A2) as [|x2 l2]; [contradiction |].
      simpl in Hleaf. injection Hleaf as _ Hrest.
      destruct l1; simpl in Hrest; discriminate.
Qed.

Lemma conts_at_stable : forall A k, gStable A -> conts_at A k = conts_at_g A k.
Proof.
  intros A (c,[v|]) Hst; simpl.
  - apply out_conts_stable; exact Hst.
  - apply in_conts_stable; exact Hst.
Qed.

Lemma klist_nonempty : forall l,
  Forall (fun p : act_key * list proc => p.2 <> []) (klist l).
Proof.
  induction l as [|a l IH]; simpl; [constructor |].
  destruct a; try exact IH; (constructor; [simpl; discriminate | exact IH]).
Qed.

(* A stable leaf is derivably below a duplicate-free association list   *)
(* carrying exactly its own continuations.                              *)
Theorem ax_M_below_leaf : forall A, gStatic A -> gStable A ->
  exists kl,
    Forall (fun p : act_key * list proc => Forall Static p.2) kl
    /\ Forall (fun p : act_key * list proc => p.2 <> []) kl
    /\ kfind_dup kl = None
    /\ (forall k p, kmem kl k p <-> p ∈ conts_at A k)
    /\ ax_pre (g A) (g (build kl)).
Proof.
  intros A Hs Hst.
  assert (Hls : Forall gStatic (summands A)) by (apply summands_gStatic; exact Hs).
  assert (Hlb : Forall gStable (summands A)).
  { apply Forall_forall. intros x Hx. eapply gStable_summands; eassumption. }
  assert (Hlf := summands_leaves A).
  assert (Hstep : ax_pre (g A) (g (build (klist (summands A))))).
  { eapply ax_trans.
    - eapply ax_cgr; [| apply summands_cgr].
      constructor. apply rebuild_gStatic. exact Hls.
    - apply ax_leaf_to_build; assumption. }
  destruct (kcollapse (length (klist (summands A))) (klist (summands A))
              (le_n _) (klist_Static _ Hls) (klist_nonempty _))
    as (kl & Hst1 & Hst2 & Hdup & Hmem & Hax).
  exists kl. split; [exact Hst1 |]. split; [exact Hst2 |]. split; [exact Hdup |].
  split.
  - intros k p. rewrite Hmem. rewrite (kmem_klist _ Hlf).
    rewrite conts_at_stable by exact Hst. symmetry. apply conts_at_g_summands.
  - eapply ax_trans; [exact Hstep | exact Hax].
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the key set of an association list, and how [krestrict]     *)
(* interacts with it.                                                  *)

Lemma kmem_khas : forall (kl : list (act_key * list proc)) k p, kmem kl k p -> khas kl k.
Proof. intros kl k p (l & Hin & _). exists l. exact Hin. Qed.

Lemma khas_kkeys : forall (kl : list (act_key * list proc)) k,
  khas kl k <-> k ∈ map fst kl.
Proof.
  induction kl as [|(k0,l0) kl' IH]; intro k; simpl.
  - split; [intros (l & Hl); set_solver | intro H; set_solver].
  - split.
    + intros (l & Hl). apply elem_of_cons in Hl. destruct Hl as [Heq|Hl].
      * injection Heq as H1 H2. subst. apply elem_of_cons; left; reflexivity.
      * apply elem_of_cons; right. apply IH. exists l. exact Hl.
    + intro H. apply elem_of_cons in H. destruct H as [Heq|H].
      * subst. exists l0. apply elem_of_cons; left; reflexivity.
      * destruct (proj2 (IH k) H) as (l & Hl). exists l. apply elem_of_cons; right; exact Hl.
Qed.

Lemma khas_krestrict : forall S (kl : list (act_key * list proc)) k,
  khas (krestrict S kl) k <-> k ∈ S /\ khas kl k.
Proof.
  intros S kl k. induction kl as [|(k0,l0) kl' IH]; simpl.
  - split; [intros (l & Hl); set_solver | intros (_ & (l & Hl)); set_solver].
  - destruct (decide (k0 ∈ S)) as [He|He].
    + split.
      * intros (l & Hl). apply elem_of_cons in Hl. destruct Hl as [Heq|Hl].
        { injection Heq as H1 H2. subst.
          split; [exact He | exists l0; apply elem_of_cons; left; reflexivity]. }
        { destruct (proj1 IH (ex_intro _ l Hl)) as (Hs & (l1 & Hl1)).
          split; [exact Hs | exists l1; apply elem_of_cons; right; exact Hl1]. }
      * intros (Hs & (l & Hl)). apply elem_of_cons in Hl. destruct Hl as [Heq|Hl].
        { injection Heq as H1 H2. subst. exists l0. apply elem_of_cons; left; reflexivity. }
        { destruct (proj2 IH (conj Hs (ex_intro _ l Hl))) as (l1 & Hl1).
          exists l1. apply elem_of_cons; right; exact Hl1. }
    + split.
      * intro H. destruct (proj1 IH H) as (Hs & (l1 & Hl1)).
        split; [exact Hs | exists l1; apply elem_of_cons; right; exact Hl1].
      * intros (Hs & (l & Hl)). apply elem_of_cons in Hl. destruct Hl as [Heq|Hl].
        { injection Heq as H1 H2. subst. contradiction. }
        { apply IH. split; [exact Hs | exists l; exact Hl]. }
Qed.

Lemma kfind_dup_krestrict : forall S (kl : list (act_key * list proc)),
  kfind_dup kl = None -> kfind_dup (krestrict S kl) = None.
Proof.
  intros S kl. induction kl as [|(k0,l0) kl' IH]; intro H; simpl; [reflexivity |].
  simpl in H. destruct (kpick k0 kl') as [(l2,r)|] eqn:E; [discriminate |].
  destruct (kfind_dup kl') as [(((a,b),c),d)|] eqn:E2; [discriminate |].
  destruct (decide (k0 ∈ S)) as [He|He]; [| apply IH; reflexivity].
  simpl. rewrite (kpick_none_conv k0 (krestrict S kl')).
  - rewrite (IH eq_refl). reflexivity.
  - intro Hc. apply khas_krestrict in Hc. destruct Hc as (_ & Hc).
    apply (kpick_none _ _ E). exact Hc.
Qed.

Lemma krestrict_sub : forall S1 S2 (kl : list (act_key * list proc)),
  (forall k, k ∈ S1 -> k ∈ S2) ->
  krestrict S1 (krestrict S2 kl) = krestrict S1 kl.
Proof.
  intros S1 S2 kl Hsub. induction kl as [|(k0,l0) kl' IH]; simpl; [reflexivity |].
  destruct (decide (k0 ∈ S2)) as [H2|H2]; simpl.
  - destruct (decide (k0 ∈ S1)); [rewrite IH; reflexivity | exact IH].
  - destruct (decide (k0 ∈ S1)) as [H1|H1]; [exfalso; apply H2; apply Hsub; exact H1 | exact IH].
Qed.

Lemma kmap_gStatic : forall (kl : list (act_key * list proc)),
  Forall (fun p : act_key * list proc => Forall Static p.2) kl ->
  Forall gStatic (map (fun p : act_key * list proc => kguard p.1 p.2) kl).
Proof.
  induction kl as [|(k,l) kl' IH]; intro H; simpl; [constructor |].
  inversion H as [|? ? Ha H']; subst.
  constructor; [apply kguard_gStatic; exact Ha | apply IH; exact H'].
Qed.

(** Convexity, in the association-list view.  This is where [ax_convex]
    is finally used: a target restricted to a *smaller* action set [S1]
    and the full target together dominate the target at any [S] in
    between.  The two restrictions really are sub-sums of the full one
    ([krestrict_split]), which is exactly what the rule requires. *)
Lemma ax_convex_build : forall S1 S (kl : list (act_key * list proc)) q,
  Forall (fun p : act_key * list proc => Forall Static p.2) kl ->
  (forall k, k ∈ S1 -> k ∈ S) ->
  ax_pre q (g (build (krestrict S1 kl))) ->
  ax_pre q (g (build kl)) ->
  ax_pre q (g (build (krestrict S kl))).
Proof.
  intros S1 S kl q Hst Hsub H1 H2.
  set (Y := map (fun p : act_key * list proc => kguard p.1 p.2) (kexclude S1 (krestrict S kl))).
  set (Z := map (fun p : act_key * list proc => kguard p.1 p.2) (kexclude S kl)).
  assert (Hperm : Permutation kl
                    (krestrict S1 kl ++ (kexclude S1 (krestrict S kl) ++ kexclude S kl))).
  { etransitivity; [apply (krestrict_split S kl) |].
    rewrite app_assoc. apply Permutation_app_tail.
    rewrite <- (krestrict_sub S1 S kl Hsub). apply krestrict_split. }
  eapply ax_trans; [apply ax_int_glb; [exact H1 | exact H2] |].
  eapply ax_trans;
    [apply (ax_convex_anywhere (build kl) (build (krestrict S1 kl)) Y Z) |].
  - apply build_gStatic. apply krestrict_Forall. exact Hst.
  - apply kmap_gStatic. apply kexclude_Forall. apply krestrict_Forall. exact Hst.
  - apply kmap_gStatic. apply kexclude_Forall. exact Hst.
  - rewrite !summands_build.
    etransitivity; [apply Permutation_app_tail; apply Permutation_map; exact Hperm |].
    rewrite !map_app. unfold Y, Z.
    rewrite <- !app_assoc. apply Permutation_app_head.
    change ([𝟘] ++ map (fun p : act_key * list proc => kguard p.1 p.2)
                     (kexclude S1 (krestrict S kl)) ++
              map (fun p : act_key * list proc => kguard p.1 p.2) (kexclude S kl))
      with (𝟘 :: (map (fun p : act_key * list proc => kguard p.1 p.2)
                    (kexclude S1 (krestrict S kl)) ++
              map (fun p : act_key * list proc => kguard p.1 p.2) (kexclude S kl))).
    rewrite app_assoc. symmetry. apply Permutation_cons_append.
  - eapply ax_cgr.
    + constructor. apply build_gStatic. apply krestrict_Forall. exact Hst.
    + etransitivity;
        [apply cgr_symm;
         apply (rebuild_app
                  (map (fun p : act_key * list proc => kguard p.1 p.2) (krestrict S1 kl)) Y) |].
      apply rebuild_perm. unfold Y. rewrite <- map_app.
      apply Permutation_map. rewrite <- (krestrict_sub S1 S kl Hsub) at 1.
      symmetry. apply krestrict_split.
Qed.

Lemma khas_kmem : forall (kl : list (act_key * list proc)) k,
  Forall (fun p : act_key * list proc => p.2 <> []) kl ->
  khas kl k -> exists p, kmem kl k p.
Proof.
  intros kl k Hne (l & Hl).
  assert (Hl2 : l <> []).
  { rewrite Forall_forall in Hne. exact (Hne (k,l) Hl). }
  destruct l as [|p l']; [contradiction |].
  exists p. exists (p :: l'). split; [exact Hl | apply elem_of_cons; left; reflexivity].
Qed.

(** The ⊕-node's core, stated without reference to [M] at all.

    [klA] is one branch's list *already restricted* to the action set
    [S] the node has to land on, [klB] is the other branch's full list,
    and [klfull] carries both.  Sharing ([kshare_iter]) pools [klB]'s
    continuations into [klA]'s keys — the uniformity step, and the only
    place [ax_share_in]/[ax_share_out] are used — so the result has the
    *first* branch's ready set and *both* branches' continuations.
    [ax_build_align] turns it into a genuine sub-list of [klfull], and
    [ax_convex_build] then moves from that sub-list up to [S]. *)
Lemma ax_share_restrict : forall S (klA klB klfull : list (act_key * list proc)) (q : proc),
  Forall (fun p : act_key * list proc => Forall Static p.2) klA ->
  Forall (fun p : act_key * list proc => p.2 <> []) klA ->
  Forall (fun p : act_key * list proc => Forall Static p.2) klB ->
  Forall (fun p : act_key * list proc => p.2 <> []) klB ->
  Forall (fun p : act_key * list proc => Forall Static p.2) klfull ->
  Forall (fun p : act_key * list proc => p.2 <> []) klfull ->
  kfind_dup klfull = None ->
  (forall k p, kmem klfull k p <-> kmem klA k p \/ kmem klB k p) ->
  ax_pre q (g (build (krestrict S klA))) ->
  ax_pre q (g (build klB)) ->
  ax_pre q (g (build klfull)) ->
  ax_pre q (g (build (krestrict S klfull))).
Proof.
  intros S klA klB klfull q HA1 HA2 HB1 HB2 HF1 HF2 Hdup Hunion HrA HB Hfull.
  set (S' := map fst (krestrict S klA)).
  assert (HsubS : forall k, k ∈ S' -> k ∈ S).
  { intros k Hk. apply khas_kkeys in Hk. apply khas_krestrict in Hk. tauto. }
  assert (Htodo : forall e : act_key * list proc, e ∈ klB -> exists r, Permutation klB (e :: r)).
  { intros e He. apply elem_of_Permutation. exact He. }
  destruct (kshare_iter klB (krestrict S klA) klB q
              (krestrict_Forall _ _ _ HA1) (krestrict_Forall _ _ _ HA2) HB1 HB2
              Htodo HrA HB)
    as (klsh & Hsh1 & Hsh2 & Hshkeys & Hshmono & Hshpool & Hshinv & Hshax).
  destruct (kcollapse (length klsh) klsh (le_n _) Hsh1 Hsh2)
    as (klsh' & Hc1 & Hc2 & Hcdup & Hcmem & Hcax).
  assert (Hax1 : ax_pre q (g (build klsh'))) by (eapply ax_trans; [exact Hshax | exact Hcax]).
  assert (HkeyS' : forall k, khas klsh k <-> k ∈ S').
  { intro k. rewrite Hshkeys. apply khas_kkeys. }
  assert (Hmem : forall k p, kmem klsh' k p <-> kmem (krestrict S' klfull) k p).
  { intros k p. rewrite Hcmem, kmem_krestrict, Hunion. split.
    - intro H. split.
      + apply HkeyS'. eapply kmem_khas; exact H.
      + destruct (Hshinv _ _ H) as [H'|H']; [left | right; exact H'].
        apply kmem_krestrict in H'. tauto.
    - intros (Hk & [H'|H']).
      + apply Hshmono. apply kmem_krestrict. split; [apply HsubS; exact Hk | exact H'].
      + destruct H' as (l & Hl & Hp).
        apply (Hshpool (k,l) Hl); [simpl; apply khas_kkeys; exact Hk | exact Hp]. }
  assert (Halign : ax_pre (g (build klsh')) (g (build (krestrict S' klfull)))).
  { apply (ax_build_align (length klsh')); try assumption.
    - apply le_n.
    - apply krestrict_Forall; exact HF1.
    - apply krestrict_Forall; exact HF2.
    - apply kfind_dup_krestrict; exact Hdup.
    - intro k. split.
      + intro H. destruct (khas_kmem _ _ Hc2 H) as (p & Hp).
        eapply kmem_khas. apply Hmem. exact Hp.
      + intro H. destruct (khas_kmem _ _ (krestrict_Forall _ _ _ HF2) H) as (p & Hp).
        eapply kmem_khas. apply Hmem. exact Hp. }
  eapply ax_convex_build; [exact HF1 | exact HsubS | | exact Hfull].
  eapply ax_trans; [exact Hax1 | exact Halign].
Qed.

(* ------------------------------------------------------------------ *)
(* The main induction over [tau_nf].                                    *)

Lemma leaves_choice : forall M1 M2,
  leaves ((𝛕 • (g M1)) + (𝛕 • (g M2))) = leaves M1 ++ leaves M2.
Proof. intros M1 M2. rewrite leaves_eq. reflexivity. Qed.

Lemma in_conts_list_app : forall l1 l2 c,
  in_conts_list (l1 ++ l2) c = in_conts_list l1 c ++ in_conts_list l2 c.
Proof.
  induction l1 as [|a l1 IH]; intros l2 c; simpl; [reflexivity |].
  rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma out_conts_list_app : forall l1 l2 c v,
  out_conts_list (l1 ++ l2) c v = out_conts_list l1 c v ++ out_conts_list l2 c v.
Proof.
  induction l1 as [|a l1 IH]; intros l2 c v; simpl; [reflexivity |].
  rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma conts_at_choice : forall M1 M2 k,
  conts_at ((𝛕 • (g M1)) + (𝛕 • (g M2))) k = conts_at M1 k ++ conts_at M2 k.
Proof.
  intros M1 M2 (c,[v|]); simpl; unfold out_conts, in_conts;
    rewrite leaves_choice; [apply out_conts_list_app | apply in_conts_list_app].
Qed.

Lemma krestrict_all : forall S (kl : list (act_key * list proc)),
  (forall e : act_key * list proc, e ∈ kl -> fst e ∈ S) -> krestrict S kl = kl.
Proof.
  intros S kl. induction kl as [|(k,l) kl' IH]; intro H; simpl; [reflexivity |].
  destruct (decide (k ∈ S)) as [He|He].
  - rewrite IH; [reflexivity | intros e He2; apply H; apply elem_of_cons; right; exact He2].
  - exfalso. apply He. apply (H (k,l)). apply elem_of_cons; left; reflexivity.
Qed.

Lemma gStatic_tau_choice : forall M1 M2,
  gStatic ((𝛕 • (g M1)) + (𝛕 • (g M2))) -> gStatic M1 /\ gStatic M2.
Proof.
  intros M1 M2 H. inversion H; subst.
  match goal with HA : gStatic (𝛕 • (g M1)) |- _ => inversion HA; subst end.
  match goal with HB : gStatic (𝛕 • (g M2)) |- _ => inversion HB; subst end.
  match goal with HA : Static (g M1) |- _ => inversion HA; subst end.
  match goal with HB : Static (g M2) |- _ => inversion HB; subst end.
  split; assumption.
Qed.

(** Every normal form is derivably below a duplicate-free association
    list carrying *all* of its continuations — and below every
    restriction of that list to an action set containing some leaf's
    actions.

    The restricted part is what the level above consumes: at an
    ⊕-node it is the first branch's contribution, and it is what
    [ax_convex_build] needs as its sub-sum.  Stating it against
    [krestrict S kl] — a genuine sub-list of [kl] — is exactly what
    makes it consumable.

    Leaf case: [ax_M_below_leaf], after which [krestrict S kl = kl]
    because every key of [kl] carries a continuation of [A].
    ⊕-node: the two branch lists, merged by [kcollapse] for the full
    part; [ax_share_restrict] for the restricted one. *)
Theorem ax_M_below : forall M, tau_nf M -> gStatic M ->
  exists kl,
    Forall (fun p : act_key * list proc => Forall Static p.2) kl
    /\ Forall (fun p : act_key * list proc => p.2 <> []) kl
    /\ kfind_dup kl = None
    /\ (forall k p, kmem kl k p <-> p ∈ conts_at M k)
    /\ ax_pre (g M) (g (build kl))
    /\ (forall S, (exists A, A ∈ leaves M /\ (forall k, conts_at A k <> [] -> k ∈ S)) ->
          ax_pre (g M) (g (build (krestrict S kl)))).
Proof.
  intros M Htnf. induction Htnf as [A Hstb | M1 M2 Ht1 IH1 Ht2 IH2]; intro Hs.
  - destruct (ax_M_below_leaf A Hs Hstb) as (kl & H1 & H2 & H3 & H4 & H5).
    exists kl. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [exact H4|]. split; [exact H5|].
    intros S (A' & HA' & Hkeys).
    rewrite (leaves_stable_self A Hstb) in HA'.
    assert (A' = A) by set_solver. subst A'.
    rewrite krestrict_all; [exact H5 |].
    intros (k,l) He. simpl.
    assert (Hne : l <> []) by (rewrite Forall_forall in H2; exact (H2 (k,l) He)).
    destruct l as [|p l']; [contradiction |].
    apply Hkeys. intro Hc.
    assert (Hm : kmem kl k p)
      by (exists (p::l'); split; [exact He | apply elem_of_cons; left; reflexivity]).
    apply H4 in Hm. rewrite Hc in Hm. set_solver.
  - destruct (gStatic_tau_choice M1 M2 Hs) as (Hs1 & Hs2).
    destruct (IH1 Hs1) as (kl1 & A1 & B1 & C1 & D1 & E1 & F1).
    destruct (IH2 Hs2) as (kl2 & A2 & B2 & C2 & D2 & E2 & F2).
    assert (Hax1 : ax_pre (g ((𝛕 • (g M1)) + (𝛕 • (g M2)))) (g (build kl1)))
      by (eapply ax_trans; [apply ax_int_l | exact E1]).
    assert (Hax2 : ax_pre (g ((𝛕 • (g M1)) + (𝛕 • (g M2)))) (g (build kl2)))
      by (eapply ax_trans; [apply ax_int_r | exact E2]).
    assert (HappS : Forall (fun p : act_key * list proc => Forall Static p.2) (kl1 ++ kl2))
      by (apply Forall_app; split; assumption).
    assert (HappN : Forall (fun p : act_key * list proc => p.2 <> []) (kl1 ++ kl2))
      by (apply Forall_app; split; assumption).
    destruct (kcollapse (length (kl1++kl2)) (kl1++kl2) (le_n _) HappS HappN)
      as (kl & G1 & G2 & G3 & G4 & G5).
    assert (Hunion : forall k p, kmem kl k p <-> kmem kl1 k p \/ kmem kl2 k p).
    { intros k p. rewrite G4. apply kmem_app. }
    assert (Hfull : ax_pre (g ((𝛕 • (g M1)) + (𝛕 • (g M2)))) (g (build kl))).
    { eapply ax_trans; [apply ax_int_glb; [exact Hax1 | exact Hax2] |].
      eapply ax_trans; [apply ax_int_below_ext; apply build_gStatic; assumption |].
      eapply ax_trans; [| exact G5].
      eapply ax_cgr; [constructor; apply build_gStatic; exact HappS |].
      apply cgr_symm. apply cgr_build_app. }
    exists kl. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    split; [| split; [exact Hfull |]].
    + intros k p. rewrite Hunion, D1, D2, conts_at_choice. symmetry. apply elem_of_app.
    + intros S (A & HA & Hkeys).
      rewrite leaves_choice in HA. apply elem_of_app in HA. destruct HA as [HA|HA].
      * eapply (ax_share_restrict S kl1 kl2 kl); try assumption.
        eapply ax_trans; [apply ax_int_l | apply F1; exists A; split; assumption].
      * eapply (ax_share_restrict S kl2 kl1 kl); try assumption.
        { intros k p. rewrite Hunion. tauto. }
        { eapply ax_trans; [apply ax_int_r | apply F2; exists A; split; assumption]. }
Qed.

(* ------------------------------------------------------------------ *)
(* From an association list to an arbitrary stable sum over the same    *)
(* guards — duplicates and [𝟘]-padding included.                       *)
(*                                                                     *)
(* [build kl] carries one summand per key, whereas the sum the final    *)
(* matching is stated against is read off the *right-hand side*'s       *)
(* summands, which may repeat an action and may contain [𝟘]/[①].       *)
(* Bridging the two needs exactly one new derived law: a guard may be   *)
(* duplicated.                                                         *)

(** A stable leaf guard is derivably below its own doubling.  For the
    two prefixes this is the distributivity law read backwards, with
    [ax_int_glb] supplying the degenerate internal choice [P ⊕ P]; for
    [①] it goes through [ax_success_l]/[_r], which is the second place
    those rules are needed. *)
Lemma ax_dup_guard : forall a, gStatic a -> gStable a -> summands a = [a] ->
  ax_pre (g a) (g (a + a)).
Proof.
  intros a Hs Hst Hleaf.
  destruct a as [ | | c P | c v P | P | A1 A2 ].
  - assert (H1 : ax_pre (g (𝟘 : gproc)) (g ((𝟘 : gproc) + 𝟘))).
    { eapply ax_cgr; [repeat constructor | apply cgr_choice_nil_rev]. }
    assert (H2 : ax_pre (g ((𝟘 : gproc) + 𝟘)) (g ((① : gproc) + 𝟘))).
    { apply (ax_choice_stable 𝟘 ① 𝟘); [exact I | exact I | apply ax_success_r]. }
    assert (H3 : ax_pre (g ((① : gproc) + 𝟘)) (g ((𝟘 : gproc) + ①))).
    { eapply ax_cgr; [repeat constructor | apply cgr_choice_com]. }
    assert (H4 : ax_pre (g ((𝟘 : gproc) + ①)) (g ((① : gproc) + ①))).
    { apply (ax_choice_stable 𝟘 ① ①); [exact I | exact I | apply ax_success_r]. }
    eapply ax_trans; [apply ax_success_l |].
    eapply ax_trans; [exact H1 |]. eapply ax_trans; [exact H2 |].
    eapply ax_trans; [exact H3 |]. exact H4.
  - eapply ax_cgr; [repeat constructor | apply cgr_choice_nil_rev].
  - eapply ax_trans; [| apply ax_input_distrib_r].
    apply ax_input. intro v. simpl. apply ax_int_glb; apply ax_refl.
  - eapply ax_trans; [| apply ax_output_distrib_r].
    apply ax_output. apply ax_int_glb; apply ax_refl.
  - simpl in Hst. contradiction.
  - exfalso. simpl in Hleaf.
    assert (H1 := summands_nonempty A1). assert (H2 := summands_nonempty A2).
    destruct (summands A1) as [|x1 l1]; [contradiction |].
    destruct (summands A2) as [|x2 l2]; [contradiction |].
    simpl in Hleaf. injection Hleaf as _ Hrest. destruct l1; simpl in Hrest; discriminate.
Qed.

(** Adding a summand that is *already present* changes nothing.  Note
    the shape: [ax_choice_stable] only rewrites the leftmost summand, so
    the target is pulled to the front first ([pull_one]). *)
Lemma ax_add_dups : forall X a, gStatic X -> gStable X -> a ∈ summands X ->
  ax_pre (g X) (g (a + X)).
Proof.
  intros X a Hs Hst Hin.
  assert (Hsa : gStatic a).
  { pose proof (summands_gStatic X Hs) as H. rewrite Forall_forall in H. exact (H a Hin). }
  assert (Hsta : gStable a) by (exact (gStable_summands X Hst a Hin)).
  assert (Hlf : summands a = [a]).
  { pose proof (summands_leaves X) as H. rewrite Forall_forall in H. exact (H a Hin). }
  assert (Hsr : Forall gStatic (summands X)) by (apply summands_gStatic; exact Hs).
  assert (Hstr : Forall gStable (summands X)).
  { apply Forall_forall. intros x Hx. exact (gStable_summands X Hst x Hx). }
  apply elem_of_Permutation in Hin. destruct Hin as (r & Hperm).
  assert (Hcgr := pull_one X a r Hperm).
  rewrite Hperm in Hsr, Hstr.
  inversion Hsr as [|? ? _ Hsr']; subst. inversion Hstr as [|? ? _ Hstr']; subst.
  eapply ax_trans.
  { eapply ax_cgr; [| exact Hcgr].
    repeat constructor; [exact Hsa | apply rebuild_gStatic; exact Hsr']. }
  eapply ax_trans.
  { apply (ax_choice_stable a (a + a) (rebuild r));
      [exact Hsta | simpl; split; exact Hsta | apply ax_dup_guard; assumption]. }
  eapply ax_cgr.
  - repeat constructor; [exact Hsa | exact Hs].
  - etransitivity; [apply cgr_choice_assoc |].
    apply cgr_fullchoice; [apply cgr_refl | apply cgr_symm; exact Hcgr].
Qed.

Lemma kguard_not_nil : forall k l, kguard k l <> (𝟘 : gproc).
Proof. intros (c,[v|]) l; simpl; discriminate. Qed.

Lemma kguard_key_inj : forall k k' l l', kguard k l = kguard k' l' -> k = k'.
Proof.
  intros (c,[v|]) (c',[v'|]) l l' H; simpl in H; try discriminate;
    injection H as H1 H2; subst; reflexivity.
Qed.

Lemma cgr_build_perm : forall kl kl', Permutation kl kl' ->
  cgr 0 (g (build kl)) (g (build kl')).
Proof. intros kl kl' H. apply rebuild_perm. apply Permutation_map. exact H. Qed.

Lemma kguard_leafP : forall k l, summands (kguard k l) = [kguard k l].
Proof. intros (c,[v|]) l; reflexivity. Qed.

Lemma gact_kguard : forall k l, gact (kguard k l) = Some k.
Proof. intros (c,[v|]) l; reflexivity. Qed.

Lemma kfind_dup_unique : forall (kl : list (act_key * list proc)) k l l',
  kfind_dup kl = None -> (k,l) ∈ kl -> (k,l') ∈ kl -> l = l'.
Proof.
  induction kl as [|(k0,l0) kl' IH]; intros k l l' Hd H1 H2; [set_solver |].
  simpl in Hd. destruct (kpick k0 kl') as [(a,b)|] eqn:E; [discriminate |].
  destruct (kfind_dup kl') as [(((x,y),z),t)|] eqn:E2; [discriminate |].
  apply elem_of_cons in H1. apply elem_of_cons in H2.
  destruct H1 as [He1|H1]; destruct H2 as [He2|H2].
  - injection He1 as ? ?; injection He2 as ? ?; subst; reflexivity.
  - injection He1 as ? ?; subst. exfalso. apply (kpick_none _ _ E). exists l'. exact H2.
  - injection He2 as ? ?; subst. exfalso. apply (kpick_none _ _ E). exists l. exact H1.
  - exact (IH k l l' eq_refl H1 H2).
Qed.

Lemma lw_props : forall (lw : list gproc) (kl : list (act_key * list proc)),
  Forall (fun p : act_key * list proc => Forall Static p.2) kl ->
  (forall w, w ∈ lw -> w = (𝟘 : gproc) \/
       exists e : act_key * list proc, e ∈ kl /\ w = kguard e.1 e.2) ->
  Forall gStatic lw /\ Forall gStable lw /\ Forall (fun a : gproc => summands a = [a]) lw.
Proof.
  intros lw kl Hkl Hi.
  split; [| split]; apply Forall_forall; intros w Hw; destruct (Hi w Hw) as [->|(e & He & ->)].
  - constructor.
  - apply kguard_gStatic. rewrite Forall_forall in Hkl. exact (Hkl e He).
  - exact I.
  - apply kguard_gStable.
  - reflexivity.
  - apply kguard_leafP.
Qed.

(** [build kl] is derivably below *any* stable sum whose summands are
    [𝟘]s and [kguard]s of [kl]'s own entries, provided every entry is
    represented at least once.  Repetitions are absorbed by
    [ax_add_dups], [𝟘]s by [≡*].

    The recursion peels [lw]'s head; the interesting choice is whether
    that head's key occurs again later — decided on [gact] (which has
    decidable equality) rather than on [gproc] (which does not). *)
Theorem ax_build_to_list : forall (lw : list gproc) (kl : list (act_key * list proc)),
  Forall (fun p : act_key * list proc => Forall Static p.2) kl ->
  kfind_dup kl = None ->
  (forall w, w ∈ lw -> w = (𝟘 : gproc) \/
       exists e : act_key * list proc, e ∈ kl /\ w = kguard e.1 e.2) ->
  (forall e : act_key * list proc, e ∈ kl -> kguard e.1 e.2 ∈ lw) ->
  ax_pre (g (build kl)) (g (rebuild lw)).
Proof.
  induction lw as [|w lw' IH]; intros kl Hkl Hdup Hi Hii.
  - destruct kl as [|e kl']; [apply ax_refl |].
    exfalso. assert (He0 : e ∈ e :: kl') by (apply elem_of_cons; left; reflexivity).
    assert (H := Hii e He0). set_solver.
  - assert (Hw0 : w ∈ w :: lw') by (apply elem_of_cons; left; reflexivity).
    assert (Hi' : forall x, x ∈ lw' -> x = (𝟘 : gproc) \/
       exists e : act_key * list proc, e ∈ kl /\ x = kguard e.1 e.2)
      by (intros x Hx; apply Hi; apply elem_of_cons; right; exact Hx).
    destruct (lw_props lw' kl Hkl Hi') as (Hsl1 & Hsl2 & Hsl3).
    assert (Hrs : gStatic (rebuild lw')) by (apply rebuild_gStatic; exact Hsl1).
    assert (Hrb : gStable (rebuild lw')) by (apply gStable_rebuild; exact Hsl2).
    pose proof Hkl as HklF. rewrite Forall_forall in HklF.
    destruct (Hi w Hw0) as [Hw | ((ke,le) & He & Hw)].
    + subst w. eapply ax_trans.
      * apply IH; try assumption.
        intros e0 He0. assert (H := Hii e0 He0). apply elem_of_cons in H.
        destruct H as [Hc|H]; [exfalso; exact (kguard_not_nil e0.1 e0.2 Hc) | exact H].
      * eapply ax_cgr; [repeat constructor; exact Hrs |].
        etransitivity; [apply cgr_choice_nil_rev | apply cgr_choice_com].
    + simpl in Hw. subst w.
      assert (Hle : Forall Static le) by (exact (HklF (ke,le) He)).
      destruct (decide (Some ke ∈ map gact lw')) as [Hd | Hd].
      * assert (Hwin : kguard ke le ∈ lw').
        { apply elem_of_map_any in Hd. destruct Hd as (x & Hx & Hgx).
          destruct (Hi' x Hx) as [Hx0 | ((k',l') & He' & Hx0)].
          - subst x. simpl in Hgx. discriminate.
          - simpl in Hx0. subst x. rewrite gact_kguard in Hgx.
            injection Hgx as Hk. subst k'.
            assert (l' = le) by (eapply kfind_dup_unique; [exact Hdup | exact He' | exact He]).
            subst l'. exact Hx. }
        assert (Hmem : kguard ke le ∈ summands (rebuild lw')).
        { rewrite (summands_rebuild_leaves lw' Hsl3). apply elem_of_app. left. exact Hwin. }
        eapply ax_trans.
        { apply IH; try assumption.
          intros e0 He0. assert (H := Hii e0 He0). apply elem_of_cons in H.
          destruct H as [Hc|H]; [| exact H].
          assert (Hkk : e0.1 = ke) by (apply (kguard_key_inj _ _ e0.2 le); exact Hc).
          destruct e0 as (a,b). simpl in *. subst a.
          assert (b = le) by (eapply kfind_dup_unique; [exact Hdup | exact He0 | exact He]).
          subst b. exact Hwin. }
        apply ax_add_dups; [exact Hrs | exact Hrb | exact Hmem].
      * assert (Hkhas : khas kl ke) by (exists le; exact He).
        destruct (kpick_some ke kl Hkhas) as (l0 & r & Hpick).
        assert (Hperm := kpick_spec ke kl l0 r Hpick).
        assert (Hl0 : l0 = le).
        { eapply kfind_dup_unique; [exact Hdup | | exact He]. rewrite Hperm.
          apply elem_of_cons; left; reflexivity. }
        subst l0.
        destruct (kfind_dup_pick ke kl le r Hdup Hpick) as (Hdr & Hpr).
        assert (Hklr : Forall (fun p : act_key * list proc => Forall Static p.2) r).
        { rewrite Hperm in Hkl. inversion Hkl; assumption. }
        assert (HIH : ax_pre (g (build r)) (g (rebuild lw'))).
        { apply IH; try assumption.
          - intros x Hx. destruct (Hi' x Hx) as [Hx0 | ((k',l') & He' & Hx0)];
              [left; exact Hx0 |].
            right. exists (k',l'). split; [| exact Hx0]. simpl in Hx0.
            assert (Hne : k' <> ke).
            { intro Hc. subst k'. exfalso. apply Hd. apply elem_of_map_any.
              exists x. split; [exact Hx | subst x; symmetry; apply gact_kguard]. }
            rewrite Hperm in He'. apply elem_of_cons in He'.
            destruct He' as [Hc|Hc]; [injection Hc as ? ?; subst; contradiction | exact Hc].
          - intros e0 He0.
            assert (He0' : e0 ∈ kl) by (rewrite Hperm; apply elem_of_cons; right; exact He0).
            assert (H := Hii e0 He0'). apply elem_of_cons in H.
            destruct H as [Hc|H]; [| exact H].
            exfalso. assert (Hkk : e0.1 = ke) by (apply (kguard_key_inj _ _ e0.2 le); exact Hc).
            apply (kpick_none ke r Hpr). exists e0.2.
            destruct e0 as (a,b). simpl in *. subst a. exact He0. }
        eapply ax_trans.
        { eapply ax_cgr; [| apply (cgr_build_perm kl ((ke,le) :: r) Hperm)].
          constructor. apply build_gStatic. rewrite <- Hperm. exact Hkl. }
        eapply ax_trans.
        { eapply ax_cgr; [| apply (cgr_choice_com 0 (kguard ke le) (build r))].
          repeat constructor; [apply build_gStatic; exact Hklr | apply kguard_gStatic; exact Hle]. }
        eapply ax_trans.
        { apply ax_choice_stable; [apply build_gStable | exact Hrb | exact HIH]. }
        eapply ax_cgr; [| apply (cgr_choice_com 0 (rebuild lw') (kguard ke le))].
        repeat constructor; [apply kguard_gStatic; exact Hle | exact Hrs].
Qed.

(* ------------------------------------------------------------------ *)
(* Reading action keys off a sum's summands, and the trace-inclusion    *)
(* fact that every action the right-hand side offers is one the left    *)
(* can match.                                                          *)

Fixpoint keylist (l : list gproc) : list act_key :=
match l with
| [] => []
| a :: l' => match gact a with Some k => k :: keylist l' | None => keylist l' end
end.

Lemma keylist_spec : forall l k, k ∈ keylist l <-> exists a, a ∈ l /\ gact a = Some k.
Proof.
  induction l as [|a l IH]; intro k; simpl.
  - split; [set_solver | intros (x & Hx & _); set_solver].
  - destruct (gact a) as [k0|] eqn:E.
    + split.
      * intro H. apply elem_of_cons in H. destruct H as [->|H].
        { exists a. split; [apply elem_of_cons; left; reflexivity | exact E]. }
        { destruct (proj1 (IH k) H) as (x & Hx & Hg).
          exists x. split; [apply elem_of_cons; right; exact Hx | exact Hg]. }
      * intros (x & Hx & Hg). apply elem_of_cons in Hx. destruct Hx as [->|Hx].
        { rewrite E in Hg. injection Hg as ->. apply elem_of_cons; left; reflexivity. }
        { apply elem_of_cons; right. apply IH. exists x. split; assumption. }
    + split.
      * intro H. destruct (proj1 (IH k) H) as (x & Hx & Hg).
        exists x. split; [apply elem_of_cons; right; exact Hx | exact Hg].
      * intros (x & Hx & Hg). apply elem_of_cons in Hx. destruct Hx as [->|Hx].
        { rewrite E in Hg. discriminate. }
        { apply IH. exists x. split; assumption. }
Qed.

Lemma has_input_summand : forall M c, has_input c M -> exists P, (c ? P) ∈ summands M.
Proof.
  induction M as [ | | c0 P0 | c0 v0 P0 | P0 | M1 IH1 M2 IH2 ]; intros c H; simpl in H;
    try contradiction.
  - subst c0. exists P0. simpl. apply elem_of_cons; left; reflexivity.
  - simpl. destruct H as [H|H].
    + destruct (IH1 c H) as (P & HP). exists P. apply elem_of_app; left; exact HP.
    + destruct (IH2 c H) as (P & HP). exists P. apply elem_of_app; right; exact HP.
Qed.

Lemma has_output_summand : forall M c, has_output c M -> exists v P, (c ! v • P) ∈ summands M.
Proof.
  induction M as [ | | c0 P0 | c0 v0 P0 | P0 | M1 IH1 M2 IH2 ]; intros c H; simpl in H;
    try contradiction.
  - subst c0. exists v0, P0. simpl. apply elem_of_cons; left; reflexivity.
  - simpl. destruct H as [H|H].
    + destruct (IH1 c H) as (v & P & HP). exists v, P. apply elem_of_app; left; exact HP.
    + destruct (IH2 c H) as (v & P & HP). exists v, P. apply elem_of_app; right; exact HP.
Qed.

Lemma in_conts_g_has_input : forall A c, in_conts_g A c <> [] -> has_input c A.
Proof.
  induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IH1 A2 IH2 ]; intros c H; simpl in *;
    try (exfalso; apply H; reflexivity).
  - destruct (decide (c0 = c)) as [->|Hd]; [reflexivity | exfalso; apply H; reflexivity].
  - destruct (in_conts_g A1 c) as [|x l] eqn:E1.
    + right. apply IH2. simpl in H. exact H.
    + left. apply IH1. rewrite E1. discriminate.
Qed.

Lemma out_conts_g_has_output : forall A c v, out_conts_g A c v <> [] -> has_output c A.
Proof.
  induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IH1 A2 IH2 ]; intros c v H; simpl in *;
    try (exfalso; apply H; reflexivity).
  - destruct (decide (c0 = c)) as [->|Hd]; [reflexivity |].
    exfalso. apply H. reflexivity.
  - destruct (out_conts_g A1 c v) as [|x l] eqn:E1.
    + right. eapply IH2. simpl in H. exact H.
    + left. eapply IH1. rewrite E1. discriminate.
Qed.

Lemma after_nonempty_from_trace : forall M N mu q,
  Static (g M) -> Static (g N) -> tau_nf M ->
  (g M) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) -> lts (g N) (ActExt mu) q -> after M mu <> [].
Proof.
  intros M N mu q HsM HsN Htnf Hpre Hlts.
  assert (Hwt : (g N) ⟹[[mu]] q) by (eapply wt_act; [exact Hlts | apply wt_nil]).
  destruct (must_i_trace_incl _ _ HsM HsN Hpre [mu] q Hwt) as (p' & Hp').
  destruct (leaves_wt_cons M Htnf mu [] p' Hp') as (A & p & HA & Hlts2 & _).
  intro Hc.
  assert (Hin : p ∈ after M mu) by (apply after_list_spec; exists A; split; assumption).
  rewrite Hc in Hin. set_solver.
Qed.

(** Every action the right-hand side offers has a continuation on the
    left.  This is where trace inclusion ([must_i_trace_incl]) pays for
    itself: without it the mirror could carry an empty [ichoice] at some
    key, and [in_cont_below]/[out_cont_below] would not apply. *)
Lemma conts_at_nonempty : forall M N a k,
  Static (g M) -> Static (g N) -> tau_nf M -> (g M) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  a ∈ summands N -> gact a = Some k -> conts_at M k <> [].
Proof.
  intros M N a k HsM HsN Htnf Hpre Ha Hg.
  destruct a as [ | | c P | c v P | P | A1 A2 ]; simpl in Hg; try discriminate.
  - injection Hg as Hk. subst k. simpl.
    assert (Hlts := summand_lts_in N c P O Ha).
    assert (Hne := after_nonempty_from_trace M N _ _ HsM HsN Htnf Hpre Hlts).
    intro Hc. apply Hne.
    apply elem_of_nil_inv. intros x Hx.
    apply in_conts_after in Hx. rewrite Hc in Hx. simpl in Hx. set_solver.
  - injection Hg as Hk. subst k. simpl.
    assert (Hlts := summand_lts_out N c v P Ha).
    assert (Hne := after_nonempty_from_trace M N _ _ HsM HsN Htnf Hpre Hlts).
    intro Hc. apply Hne.
    apply elem_of_nil_inv. intros x Hx.
    apply out_conts_after in Hx. rewrite Hc in Hx. set_solver.
Qed.

(* ------------------------------------------------------------------ *)
(* Dropping surplus output values.                                      *)
(*                                                                     *)
(* [ax_M_below]'s side condition asks for a leaf whose *keys* are all   *)
(* in [S].  What the semantics supplies is weaker — the ready-set       *)
(* abstraction erases the value, so a leaf may offer [c!v] where the    *)
(* right-hand side offers only [c!v'].  The gap is closed *after*       *)
(* [ax_M_below], by dropping the surplus output keys from the built     *)
(* sum: [ax_swap_out] makes exactly that derivable.                    *)

Lemma ax_dup_guard_rev : forall a, gStatic a -> gStable a -> summands a = [a] ->
  ax_pre (g (a + a)) (g a).
Proof.
  intros a Hs Hst Hleaf.
  destruct a as [ | | c P | c v P | P | A1 A2 ].
  - assert (H1 : ax_pre (g ((① : gproc) + ①)) (g ((𝟘 : gproc) + ①))).
    { apply (ax_choice_stable ① 𝟘 ①); [exact I | exact I | apply ax_success_l]. }
    assert (H2 : ax_pre (g ((𝟘 : gproc) + ①)) (g ((① : gproc) + 𝟘))).
    { eapply ax_cgr; [repeat constructor | apply cgr_choice_com]. }
    assert (H3 : ax_pre (g ((① : gproc) + 𝟘)) (g ((𝟘 : gproc) + 𝟘))).
    { apply (ax_choice_stable ① 𝟘 𝟘); [exact I | exact I | apply ax_success_l]. }
    assert (H4 : ax_pre (g ((𝟘 : gproc) + 𝟘)) (g (𝟘 : gproc))).
    { eapply ax_cgr; [repeat constructor | apply cgr_choice_nil]. }
    eapply ax_trans; [exact H1 |]. eapply ax_trans; [exact H2 |].
    eapply ax_trans; [exact H3 |]. eapply ax_trans; [exact H4 |].
    apply ax_success_r.
  - eapply ax_cgr; [repeat constructor | apply cgr_choice_nil].
  - eapply ax_trans; [apply ax_input_distrib_l |].
    apply ax_input. intro v. simpl. apply ax_int_l.
  - eapply ax_trans; [apply ax_output_distrib_l |].
    apply ax_output. apply ax_int_l.
  - simpl in Hst. contradiction.
  - exfalso. simpl in Hleaf.
    assert (H1 := summands_nonempty A1). assert (H2 := summands_nonempty A2).
    destruct (summands A1) as [|x1 l1]; [contradiction |].
    destruct (summands A2) as [|x2 l2]; [contradiction |].
    simpl in Hleaf. injection Hleaf as _ Hrest. destruct l1; simpl in Hrest; discriminate.
Qed.

Lemma ax_rem_dups : forall X a, gStatic X -> gStable X -> a ∈ summands X ->
  ax_pre (g (a + X)) (g X).
Proof.
  intros X a Hs Hst Hin.
  assert (Hsa : gStatic a).
  { pose proof (summands_gStatic X Hs) as H. rewrite Forall_forall in H. exact (H a Hin). }
  assert (Hsta : gStable a) by (exact (gStable_summands X Hst a Hin)).
  assert (Hlf : summands a = [a]).
  { pose proof (summands_leaves X) as H. rewrite Forall_forall in H. exact (H a Hin). }
  assert (Hsr : Forall gStatic (summands X)) by (apply summands_gStatic; exact Hs).
  apply elem_of_Permutation in Hin. destruct Hin as (r & Hperm).
  assert (Hcgr := pull_one X a r Hperm).
  rewrite Hperm in Hsr. inversion Hsr as [|? ? _ Hsr']; subst.
  eapply ax_trans.
  { eapply ax_cgr; [| apply cgr_fullchoice; [apply cgr_refl | exact Hcgr]].
    constructor. constructor;
      [exact Hsa | constructor; [exact Hsa | apply rebuild_gStatic; exact Hsr']]. }
  eapply ax_trans.
  { eapply ax_cgr; [| apply cgr_choice_assoc_rev].
    constructor. constructor;
      [constructor; [exact Hsa | exact Hsa] | apply rebuild_gStatic; exact Hsr']. }
  eapply ax_trans.
  { apply (ax_choice_stable (a + a) a (rebuild r));
      [simpl; split; exact Hsta | exact Hsta | apply ax_dup_guard_rev; assumption]. }
  eapply ax_cgr; [constructor; exact Hs | apply cgr_symm; exact Hcgr].
Qed.

(** Dropping one output summand in favour of another on the *same
    channel*.  Derived: duplicate the sum with [ax_int_glb], reassociate
    the second copy so the surviving guard is leftmost, apply
    [ax_swap_out], then remove the duplicate it leaves behind. *)
Lemma ax_drop_out : forall c v v' P Q R,
  Static P -> Static Q -> gStatic R -> gStable R ->
  ax_pre (g ((c ! v • P) + ((c ! v' • Q) + R))) (g ((c ! v' • Q) + R)).
Proof.
  intros c v v' P Q R HP HQ HR HRb.
  assert (HsA' : gStatic ((c ! v' • Q) + ((c ! v • P) + R)))
    by (repeat constructor; assumption).
  assert (Hcgr : cgr 0 (g ((c ! v • P) + ((c ! v' • Q) + R)))
                       (g ((c ! v' • Q) + ((c ! v • P) + R)))).
  { etransitivity; [apply cgr_choice_assoc_rev |].
    etransitivity; [apply cgr_choice; apply cgr_choice_com |].
    apply cgr_choice_assoc. }
  eapply ax_trans.
  { apply ax_int_glb; [apply ax_refl |].
    eapply ax_cgr; [constructor; exact HsA' | exact Hcgr]. }
  eapply ax_trans; [apply (ax_swap_out c v v' P Q ((c ! v' • Q) + R) ((c ! v • P) + R)) |].
  apply ax_rem_dups.
  - repeat constructor; assumption.
  - simpl. split; [exact I | exact HRb].
  - simpl. apply elem_of_cons. left. reflexivity.
Qed.

(** The abstraction the semantics actually constrains: channel and
    polarity, with the value erased. *)
Definition kabs (k : act_key) : ChannelData * bool :=
  match k with (c, None) => (c, false) | (c, Some _) => (c, true) end.

Lemma kabs_out : forall k k', kabs k = kabs k' -> k <> k' ->
  exists c v v', k = (c, Some v) /\ k' = (c, Some v').
Proof.
  intros (c,[v|]) (c',[v'|]) H Hne; simpl in H.
  - injection H as H1. subst c'. exists c, v, v'. split; reflexivity.
  - discriminate.
  - discriminate.
  - injection H as H1. subst c'. exfalso. apply Hne. reflexivity.
Qed.

Lemma krestrict_perm : forall S (kl kl' : list (act_key * list proc)),
  Permutation kl kl' -> Permutation (krestrict S kl) (krestrict S kl').
Proof.
  intros S kl kl' H. induction H; simpl.
  - reflexivity.
  - destruct x as (ka,la). destruct (decide (ka ∈ S)); [apply perm_skip |]; assumption.
  - destruct x as (k1,l1). destruct y as (k2,l2).
    destruct (decide (k1 ∈ S)); destruct (decide (k2 ∈ S)); simpl;
      try reflexivity; apply perm_swap.
  - etransitivity; eassumption.
Qed.

Lemma kexclude_perm : forall S (kl kl' : list (act_key * list proc)),
  Permutation kl kl' -> Permutation (kexclude S kl) (kexclude S kl').
Proof.
  intros S kl kl' H. induction H; simpl.
  - reflexivity.
  - destruct x as (ka,la). destruct (decide (ka ∈ S)); [| apply perm_skip]; assumption.
  - destruct x as (k1,l1). destruct y as (k2,l2).
    destruct (decide (k1 ∈ S)); destruct (decide (k2 ∈ S)); simpl;
      try reflexivity; apply perm_swap.
  - etransitivity; eassumption.
Qed.

Lemma kexclude_sub : forall S (kl : list (act_key * list proc)) e,
  e ∈ kexclude S kl -> e ∈ kl.
Proof.
  intros S kl. induction kl as [|(k,l) kl' IH]; intros e He; simpl in He; [set_solver |].
  destruct (decide (k ∈ S)) as [Hd|Hd].
  - apply elem_of_cons. right. apply IH. exact He.
  - apply elem_of_cons in He. destruct He as [->|He];
      [apply elem_of_cons; left; reflexivity | apply elem_of_cons; right; apply IH; exact He].
Qed.

Lemma kexclude_not_in : forall S (kl : list (act_key * list proc)) e,
  e ∈ kexclude S kl -> fst e ∉ S.
Proof.
  intros S kl. induction kl as [|(k,l) kl' IH]; intros e He; simpl in He; [set_solver |].
  destruct (decide (k ∈ S)) as [Hd|Hd]; [apply IH; exact He |].
  apply elem_of_cons in He. destruct He as [->|He]; [simpl; exact Hd | apply IH; exact He].
Qed.

Lemma kexclude_cons_notin : forall S k l (kl : list (act_key * list proc)),
  k ∉ S -> kexclude S ((k,l) :: kl) = (k,l) :: kexclude S kl.
Proof. intros S k l kl H. simpl. case_decide; [contradiction | reflexivity]. Qed.

Lemma krestrict_cons_notin : forall S k l (kl : list (act_key * list proc)),
  k ∉ S -> krestrict S ((k,l) :: kl) = krestrict S kl.
Proof. intros S k l kl H. simpl. case_decide; [contradiction | reflexivity]. Qed.

(** A built sum may be cut down to any action set that still covers
    every key *up to the abstraction* — i.e. surplus output values may
    be dropped as long as one value per channel survives.  Inputs are
    never dropped: their key *is* their abstraction.

    Measure: the number of keys outside [S], one removed per round. *)
Theorem ax_drop_keys : forall n (kl : list (act_key * list proc)) (S : list act_key),
  length (kexclude S kl) <= n ->
  Forall (fun p : act_key * list proc => Forall Static p.2) kl ->
  Forall (fun p : act_key * list proc => p.2 <> []) kl ->
  kfind_dup kl = None ->
  (forall k, khas kl k -> exists k', k' ∈ S /\ khas kl k' /\ kabs k' = kabs k) ->
  ax_pre (g (build kl)) (g (build (krestrict S kl))).
Proof.
  induction n as [|n IH]; intros kl S Hlen HS1 HS2 Hdup Hcov.
  - destruct (kexclude S kl) as [|e rest] eqn:E; [| simpl in Hlen; lia].
    eapply ax_cgr.
    + constructor. apply build_gStatic. apply krestrict_Forall. exact HS1.
    + apply cgr_build_perm. etransitivity; [apply krestrict_split |].
      rewrite E. rewrite app_nil_r. reflexivity.
  - destruct (kexclude S kl) as [|(k0,l0) rest] eqn:E.
    + eapply ax_cgr.
      * constructor. apply build_gStatic. apply krestrict_Forall. exact HS1.
      * apply cgr_build_perm. etransitivity; [apply krestrict_split |].
        rewrite E. rewrite app_nil_r. reflexivity.
    + assert (He0 : (k0,l0) ∈ kexclude S kl)
        by (rewrite E; apply elem_of_cons; left; reflexivity).
      assert (He0' : (k0,l0) ∈ kl) by (eapply kexclude_sub; exact He0).
      assert (Hk0S : k0 ∉ S) by (exact (kexclude_not_in S kl (k0,l0) He0)).
      assert (Hhas0 : khas kl k0) by (exists l0; exact He0').
      destruct (Hcov k0 Hhas0) as (k' & Hk'S & Hhas' & Habs).
      assert (Hne : k' <> k0) by (intro Hc; subst k'; contradiction).
      destruct (kabs_out k' k0 Habs Hne) as (c & v' & v & Hk' & Hk0).
      destruct (kpick_some k0 kl Hhas0) as (l0' & r0 & Hp0).
      assert (Hperm0 := kpick_spec k0 kl l0' r0 Hp0).
      assert (Hl0' : l0' = l0).
      { eapply kfind_dup_unique; [exact Hdup | | exact He0'].
        rewrite Hperm0. apply elem_of_cons; left; reflexivity. }
      subst l0'.
      destruct (kfind_dup_pick k0 kl l0 r0 Hdup Hp0) as (Hdr0 & Hpr0).
      assert (Hhasr0 : khas r0 k').
      { destruct Hhas' as (la & Hla). rewrite Hperm0 in Hla. apply elem_of_cons in Hla.
        destruct Hla as [Hc|Hla]; [injection Hc as ? ?; subst; contradiction |].
        exists la. exact Hla. }
      destruct (kpick_some k' r0 Hhasr0) as (l1 & r1 & Hp1).
      assert (Hperm1 := kpick_spec k' r0 l1 r1 Hp1).
      destruct (kfind_dup_pick k' r0 l1 r1 Hdr0 Hp1) as (Hdr1 & Hpr1).
      assert (Hpermkl : Permutation kl ((k0,l0) :: ((k',l1) :: r1))).
      { rewrite Hperm0. apply perm_skip. exact Hperm1. }
      assert (HS1c : Forall (fun p : act_key * list proc => Forall Static p.2)
                       ((k0,l0) :: ((k',l1) :: r1))) by (rewrite <- Hpermkl; exact HS1).
      assert (HS2c : Forall (fun p : act_key * list proc => p.2 <> [])
                       ((k0,l0) :: ((k',l1) :: r1))) by (rewrite <- Hpermkl; exact HS2).
      inversion HS1c as [|? ? Hl0S HS1kl2]; subst.
      inversion HS2c as [|? ? Hl0N HS2kl2]; subst.
      inversion HS1kl2 as [|? ? Hl1S HS1r1]; subst.
      simpl in Hl0S, Hl1S.
      assert (Hdup2 : kfind_dup (((c ▷ Some v') ▷ l1) :: r1) = None)
        by (simpl; rewrite Hpr1; rewrite Hdr1; reflexivity).
      assert (Hexc : Permutation (kexclude S kl)
                       (((c ▷ Some v) ▷ l0) :: kexclude S (((c ▷ Some v') ▷ l1) :: r1))).
      { etransitivity; [apply (kexclude_perm S kl _ Hpermkl) |].
        rewrite kexclude_cons_notin by exact Hk0S. reflexivity. }
      assert (Hlen2 : length (kexclude S (((c ▷ Some v') ▷ l1) :: r1)) <= n).
      { assert (HL := Permutation_length Hexc). rewrite E in HL.
        assert (HL2 : Datatypes.S (length rest)
                    = Datatypes.S (length (kexclude S (((c ▷ Some v') ▷ l1) :: r1))))
          by exact HL.
        simpl in Hlen. lia. }
      assert (Hres : Permutation (krestrict S kl)
                       (krestrict S (((c ▷ Some v') ▷ l1) :: r1))).
      { etransitivity; [apply (krestrict_perm S kl _ Hpermkl) |].
        rewrite krestrict_cons_notin by exact Hk0S. reflexivity. }
      assert (Hcov2 : forall k, khas (((c ▷ Some v') ▷ l1) :: r1) k ->
                exists k2, k2 ∈ S /\ khas (((c ▷ Some v') ▷ l1) :: r1) k2 /\ kabs k2 = kabs k).
      { intros k Hk.
        assert (Hkk : khas kl k).
        { destruct Hk as (la & Hla). exists la. rewrite Hpermkl.
          apply elem_of_cons; right; exact Hla. }
        destruct (Hcov k Hkk) as (k2 & Hk2S & Hk2has & Hk2abs).
        exists k2. split; [exact Hk2S |]. split; [| exact Hk2abs].
        destruct Hk2has as (la & Hla). rewrite Hpermkl in Hla.
        apply elem_of_cons in Hla. destruct Hla as [Hc|Hla].
        - injection Hc as ? ?; subst. contradiction.
        - exists la. exact Hla. }
      eapply ax_trans.
      { eapply ax_cgr; [| apply (cgr_build_perm kl _ Hpermkl)].
        constructor. apply build_gStatic. rewrite <- Hpermkl. exact HS1. }
      eapply ax_trans.
      { apply (ax_drop_out c v v' (g (ichoice l0)) (g (ichoice l1)) (build r1)).
        - constructor. apply ichoice_gStatic. exact Hl0S.
        - constructor. apply ichoice_gStatic. exact Hl1S.
        - apply build_gStatic. exact HS1r1.
        - apply build_gStable. }
      eapply ax_trans.
      { apply (IH (((c ▷ Some v') ▷ l1) :: r1) S); assumption. }
      eapply ax_cgr; [| apply cgr_build_perm; symmetry; exact Hres].
      constructor. apply build_gStatic. apply krestrict_Forall. exact HS1.
Qed.

(* ------------------------------------------------------------------ *)
(* Leaf selection, and looking a key up in an association list.         *)

Fixpoint klook (k : act_key) (kl : list (act_key * list proc)) : list proc :=
match kl with
| [] => []
| (k', l) :: kl' => if decide (k' = k) then l else klook k kl'
end.

Lemma klook_mem : forall (kl : list (act_key * list proc)) k,
  khas kl k -> (k, klook k kl) ∈ kl.
Proof.
  induction kl as [|(k0,l0) kl' IH]; intros k Hk; [destruct Hk as (l & Hl); set_solver |].
  simpl. destruct (decide (k0 = k)) as [->|Hd].
  - apply elem_of_cons; left; reflexivity.
  - apply elem_of_cons; right. apply IH.
    destruct Hk as (l & Hl). apply elem_of_cons in Hl.
    destruct Hl as [Hc|Hl]; [injection Hc as ? ?; subst; contradiction | exists l; exact Hl].
Qed.

Lemma klook_spec : forall (kl : list (act_key * list proc)) k l,
  kfind_dup kl = None -> (k,l) ∈ kl -> klook k kl = l.
Proof.
  intros kl k l Hdup Hin.
  assert (Hk : khas kl k) by (exists l; exact Hin).
  assert (Hin2 := klook_mem kl k Hk).
  eapply kfind_dup_unique; [exact Hdup | exact Hin2 | exact Hin].
Qed.

Lemma in_conts_g_summand : forall A c, in_conts_g A c <> [] ->
  exists P, (c ? P) ∈ summands A.
Proof.
  induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IH1 A2 IH2 ]; intros c H; simpl in *;
    try (exfalso; apply H; reflexivity).
  - destruct (decide (c0 = c)) as [->|Hd]; [| exfalso; apply H; reflexivity].
    exists P0. apply elem_of_cons; left; reflexivity.
  - destruct (in_conts_g A1 c) as [|x l] eqn:E1.
    + destruct (IH2 c H) as (P & HP). exists P. apply elem_of_app; right; exact HP.
    + destruct (IH1 c ltac:(rewrite E1; discriminate)) as (P & HP).
      exists P. apply elem_of_app; left; exact HP.
Qed.

Lemma out_conts_g_summand : forall A c v, out_conts_g A c v <> [] ->
  exists P, (c ! v • P) ∈ summands A.
Proof.
  induction A as [ | | c0 P0 | c0 v0 P0 | P0 | A1 IH1 A2 IH2 ]; intros c v H; simpl in *;
    try (exfalso; apply H; reflexivity).
  - destruct (decide (c0 = c)) as [->|Hd]; [| exfalso; apply H; reflexivity].
    destruct (decide (v0 = v)) as [->|Hv]; [| exfalso; apply H; reflexivity].
    exists P0. apply elem_of_cons; left; reflexivity.
  - destruct (out_conts_g A1 c v) as [|x l] eqn:E1.
    + destruct (IH2 c v H) as (P & HP). exists P. apply elem_of_app; right; exact HP.
    + destruct (IH1 c v ltac:(rewrite E1; discriminate)) as (P & HP).
      exists P. apply elem_of_app; left; exact HP.
Qed.

Lemma conts_at_key : forall A k, gStable A -> conts_at A k <> [] ->
  k ∈ keylist (summands A).
Proof.
  intros A (c,[v|]) Hst Hne; apply keylist_spec; simpl in Hne.
  - rewrite (out_conts_stable A c v Hst) in Hne.
    destruct (out_conts_g_summand A c v Hne) as (P & HP).
    exists (c ! v • P). split; [exact HP | reflexivity].
  - rewrite (in_conts_stable A c Hst) in Hne.
    destruct (in_conts_g_summand A c Hne) as (P & HP).
    exists (c ? P). split; [exact HP | reflexivity].
Qed.

(** [bhv_pre_cond2] at the empty trace, read as a *leaf*: some leaf of
    the normal form offers no more channels than the stable right-hand
    side.  Note this is all the semantics gives — the value is erased,
    which is what [ax_drop_keys] exists to repair. *)
Lemma leaf_from_cond2 : forall M N,
  Static (g M) -> Static (g N) -> tau_nf M -> gStable N ->
  (g M) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  exists A, A ∈ leaves M /\ gStable A /\
    (forall c, has_input c A -> has_input c N) /\
    (forall c, has_output c A -> has_output c N).
Proof.
  intros M N HsM HsN Htnf HstN Hpre.
  apply must_iff_acceptance_set_VCCS_without_toFW in Hpre.
  destruct Hpre as (Hc1 & Hc2).
  assert (HstN' : (g N) ↛) by (apply gStable_iff; exact HstN).
  destruct (Hc2 [] (g N) (Static_converge [] (g M) HsM) (wt_nil _) HstN')
    as (p' & Hwp & Hstp & Hincl).
  destruct (leaves_wt_stable M Htnf p' Hwp Hstp) as (A & HA & Heq).
  subst p'.
  exists A. split; [exact HA |].
  split; [apply gStable_iff; exact Hstp |].
  apply coR_abs_incl_iff. exact Hincl.
Qed.

Lemma leaf_keys_abs : forall (A N : gproc), gStable A ->
  (forall c, has_input c A -> has_input c N) ->
  (forall c, has_output c A -> has_output c N) ->
  forall k, conts_at A k <> [] ->
    exists k', k' ∈ keylist (summands N) /\ kabs k' = kabs k.
Proof.
  intros A N Hst Hin Hout (c,[v|]) Hne; simpl in Hne.
  - rewrite (out_conts_stable A c v Hst) in Hne.
    destruct (has_output_summand N c (Hout c (out_conts_g_has_output A c v Hne)))
      as (v2 & P & HP).
    exists (c, Some v2). split; [| reflexivity].
    apply keylist_spec. exists (c ! v2 • P). split; [exact HP | reflexivity].
  - rewrite (in_conts_stable A c Hst) in Hne.
    destruct (has_input_summand N c (Hin c (in_conts_g_has_input A c Hne))) as (P & HP).
    exists (c, None). split; [| reflexivity].
    apply keylist_spec. exists (c ? P). split; [exact HP | reflexivity].
Qed.

Lemma key_conts_at : forall A k, gStable A -> k ∈ keylist (summands A) ->
  conts_at A k <> [].
Proof.
  intros A k Hst Hk. apply keylist_spec in Hk. destruct Hk as (a & Ha & Hg).
  destruct a as [ | | c P | c v P | P | A1 A2 ]; simpl in Hg; try discriminate;
    injection Hg as Hk; subst k; simpl.
  - rewrite (in_conts_stable A c Hst).
    assert (Hlts := summand_lts_in A c P O Ha).
    apply in_conts_g_spec in Hlts. destruct Hlts as (P' & HP' & _).
    intro Hc. rewrite Hc in HP'. set_solver.
  - rewrite (out_conts_stable A c v Hst).
    assert (Hlts := summand_lts_out A c v P Ha).
    apply out_conts_g_spec in Hlts.
    intro Hc. rewrite Hc in Hlts. set_solver.
Qed.

Lemma klook_elems : forall (kl : list (act_key * list proc)) k p,
  kfind_dup kl = None -> khas kl k -> (p ∈ klook k kl <-> kmem kl k p).
Proof.
  intros kl k p Hdup Hk. split.
  - intro Hp. exists (klook k kl). split; [apply klook_mem; exact Hk | exact Hp].
  - intros (l & Hl & Hp). rewrite (klook_spec kl k l Hdup Hl). exact Hp.
Qed.

(* ------------------------------------------------------------------ *)
(* The stable-[N] step.                                                 *)

(** The left-hand summand mirroring one of [N]'s: same guard, and the
    continuation fetched from the association list at that guard's key. *)
Definition mirror_look (kl : list (act_key * list proc)) (n : gproc) : gproc :=
  match gact n with Some k => kguard k (klook k kl) | None => 𝟘 end.

(** Against a *stable* right-hand side, the whole chain:

    - [leaf_from_cond2] picks a leaf [A] of [M] whose channels are
      inside [N]'s;
    - [ax_M_below] at [S₀ := keys A ++ keys N] (the leaf's own keys are
      there, so its side condition applies);
    - [ax_drop_keys] down to [keys N] — this is where the value that
      the ready-set abstraction erased is put back, via [ax_swap_out];
    - [ax_build_to_list] re-shapes the one-summand-per-key sum into one
      summand per summand of [N] (repeats and [𝟘]s included);
    - [ax_match_lists] matches them off, each pair discharged by the
      corresponding hypothesis — which is where the recursion enters. *)
Theorem ax_stable_step : forall M N,
  gStatic M -> tau_nf M -> gStatic N -> gStable N ->
  (g M) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c Q, (c ? Q) ∈ summands N -> forall v,
      ax_pre ((g (ichoice (in_conts M c))) ^ v) (Q ^ v)) ->
  (forall c v Q, (c ! v • Q) ∈ summands N ->
      ax_pre (g (ichoice (out_conts M c v))) Q) ->
  ax_pre (g M) (g N).
Proof.
  intros M N HsM Htnf HsN HstN Hpre Hinp Houtp.
  assert (HSM : Static (g M)) by (constructor; exact HsM).
  assert (HSN : Static (g N)) by (constructor; exact HsN).
  destruct (leaf_from_cond2 M N HSM HSN Htnf HstN Hpre) as (A & HA & HstA & Hci & Hco).
  destruct (ax_M_below M Htnf HsM) as (kl & K1 & K2 & K3 & K4 & K5 & K6).
  assert (HNne : forall k, k ∈ keylist (summands N) -> conts_at M k <> []).
  { intros k Hk. apply keylist_spec in Hk. destruct Hk as (a & Ha & Hg).
    exact (conts_at_nonempty M N a k HSM HSN Htnf Hpre Ha Hg). }
  assert (HNkey : forall k, k ∈ keylist (summands N) -> khas kl k).
  { intros k Hk. assert (Hne := HNne k Hk).
    destruct (conts_at M k) as [|p l] eqn:E; [contradiction |].
    exists (klook k kl). apply klook_mem. apply (kmem_khas kl k p). apply K4.
    rewrite E. apply elem_of_cons; left; reflexivity. }
  set (SN := keylist (summands N)).
  set (S0 := keylist (summands A) ++ SN).
  assert (Hstep1 : ax_pre (g M) (g (build (krestrict S0 kl)))).
  { apply K6. exists A. split; [exact HA |].
    intros k Hk. apply elem_of_app. left. apply conts_at_key; assumption. }
  assert (HsubS : forall k, k ∈ SN -> k ∈ S0)
    by (intros k Hk; apply elem_of_app; right; exact Hk).
  assert (Hcov : forall k, khas (krestrict S0 kl) k ->
    exists k', k' ∈ SN /\ khas (krestrict S0 kl) k' /\ kabs k' = kabs k).
  { intros k Hk. apply khas_krestrict in Hk. destruct Hk as (HkS0 & Hkkl).
    apply elem_of_app in HkS0. destruct HkS0 as [HkA | HkN].
    - assert (Hne := key_conts_at A k HstA HkA).
      destruct (leaf_keys_abs A N HstA Hci Hco k Hne) as (k' & Hk'N & Hk'abs).
      exists k'. split; [exact Hk'N |]. split; [| exact Hk'abs].
      apply khas_krestrict. split; [apply HsubS; exact Hk'N | apply HNkey; exact Hk'N].
    - exists k. split; [exact HkN |]. split; [| reflexivity].
      apply khas_krestrict. split; [apply elem_of_app; right; exact HkN | exact Hkkl]. }
  assert (Hstep2 : ax_pre (g (build (krestrict S0 kl))) (g (build (krestrict SN kl)))).
  { rewrite <- (krestrict_sub SN S0 kl HsubS).
    apply (ax_drop_keys (length (kexclude SN (krestrict S0 kl)))).
    - apply le_n.
    - apply krestrict_Forall; exact K1.
    - apply krestrict_Forall; exact K2.
    - apply kfind_dup_krestrict; exact K3.
    - exact Hcov. }
  assert (Hdup' : kfind_dup (krestrict SN kl) = None)
    by (apply kfind_dup_krestrict; exact K3).
  assert (HK1' : Forall (fun p : act_key * list proc => Forall Static p.2) (krestrict SN kl))
    by (apply krestrict_Forall; exact K1).
  assert (HK2' : Forall (fun p : act_key * list proc => p.2 <> []) (krestrict SN kl))
    by (apply krestrict_Forall; exact K2).
  assert (Hkhas' : forall k, k ∈ SN -> khas (krestrict SN kl) k).
  { intros k Hk. apply khas_krestrict. split; [exact Hk | apply HNkey; exact Hk]. }
  assert (Helems : forall k p, k ∈ SN -> (p ∈ klook k (krestrict SN kl) <-> p ∈ conts_at M k)).
  { intros k p Hk. rewrite (klook_elems (krestrict SN kl) k p Hdup' (Hkhas' k Hk)).
    rewrite kmem_krestrict. rewrite K4.
    split; [tauto | intro Hp; split; [exact Hk | exact Hp]]. }
  assert (Hi : forall w, w ∈ map (mirror_look (krestrict SN kl)) (summands N) ->
      w = (𝟘 : gproc) \/
      exists e : act_key * list proc, e ∈ krestrict SN kl /\ w = kguard e.1 e.2).
  { intros w Hw. apply elem_of_map_any in Hw. destruct Hw as (a & Ha & ->).
    unfold mirror_look. destruct (gact a) as [k|] eqn:Eg; [| left; reflexivity].
    right. exists (k, klook k (krestrict SN kl)). split; [| reflexivity].
    apply klook_mem. apply Hkhas'. apply keylist_spec. exists a. split; assumption. }
  assert (Hii : forall e : act_key * list proc, e ∈ krestrict SN kl ->
      kguard e.1 e.2 ∈ map (mirror_look (krestrict SN kl)) (summands N)).
  { intros (k,l) He. simpl.
    assert (Hk : k ∈ SN).
    { assert (Hkh : khas (krestrict SN kl) k) by (exists l; exact He).
      apply khas_krestrict in Hkh. tauto. }
    apply keylist_spec in Hk. destruct Hk as (a & Ha & Hg).
    apply elem_of_map_any. exists a. split; [exact Ha |].
    unfold mirror_look. rewrite Hg.
    rewrite (klook_spec (krestrict SN kl) k l Hdup' He). reflexivity. }
  assert (Hstep3 : ax_pre (g (build (krestrict SN kl)))
                          (g (rebuild (map (mirror_look (krestrict SN kl)) (summands N))))).
  { apply ax_build_to_list; assumption. }
  destruct (lw_props (map (mirror_look (krestrict SN kl)) (summands N))
              (krestrict SN kl) HK1' Hi) as (Hlw1 & Hlw2 & _).
  eapply ax_trans; [exact Hstep1 |].
  eapply ax_trans; [exact Hstep2 |].
  eapply ax_trans; [exact Hstep3 |].
  eapply ax_trans; [| eapply ax_cgr; [exact HSN | apply cgr_symm; apply summands_cgr]].
  apply ax_match_lists.
  - exact Hlw1.
  - apply summands_gStatic; exact HsN.
  - exact Hlw2.
  - apply Forall_forall. intros x Hx. exact (gStable_summands N HstN x Hx).
  - apply Forall2_map_self. intros a Ha.
    assert (Hsta : gStable a) by (exact (gStable_summands N HstN a Ha)).
    assert (Hleaf : summands a = [a]).
    { pose proof (summands_leaves N) as H. rewrite Forall_forall in H. exact (H a Ha). }
    destruct a as [ | | c P | c v P | P | A1 A2 ].
    + unfold mirror_look. simpl. apply ax_success_r.
    + unfold mirror_look. simpl. apply ax_refl.
    + assert (HkSN : (c, None) ∈ SN)
        by (apply keylist_spec; exists (c ? P); split; [exact Ha | reflexivity]).
      assert (Hm := klook_mem (krestrict SN kl) (c,None) (Hkhas' _ HkSN)).
      assert (HLne : klook (c,None) (krestrict SN kl) <> [])
        by (rewrite Forall_forall in HK2'; exact (HK2' _ Hm)).
      assert (HLst : Forall Static (klook (c,None) (krestrict SN kl)))
        by (rewrite Forall_forall in HK1'; exact (HK1' _ Hm)).
      assert (HIne : in_conts M c <> []) by (exact (HNne _ HkSN)).
      unfold mirror_look. simpl.
      apply ax_input. intro v.
      eapply ax_trans; [| exact (Hinp c P Ha v)].
      simpl. rewrite !subst_ichoice.
      apply ax_ichoice_same_elems.
      * apply map_nonempty. exact HLne.
      * apply map_nonempty. exact HIne.
      * apply Forall_Static_subst. exact HLst.
      * apply in_conts_subst_Static. exact HsM.
      * intro p. split.
        { intro Hp. apply elem_of_map_any in Hp. destruct Hp as (x & Hx & ->).
          apply elem_of_map_any. exists x. split; [| reflexivity].
          apply (proj1 (Helems (c,None) x HkSN)). exact Hx. }
        { intro Hp. apply elem_of_map_any in Hp. destruct Hp as (x & Hx & ->).
          apply elem_of_map_any. exists x. split; [| reflexivity].
          apply (proj2 (Helems (c,None) x HkSN)). exact Hx. }
    + assert (HkSN : (c, Some v) ∈ SN)
        by (apply keylist_spec; exists (c ! v • P); split; [exact Ha | reflexivity]).
      assert (Hm := klook_mem (krestrict SN kl) (c,Some v) (Hkhas' _ HkSN)).
      assert (HLne : klook (c,Some v) (krestrict SN kl) <> [])
        by (rewrite Forall_forall in HK2'; exact (HK2' _ Hm)).
      assert (HLst : Forall Static (klook (c,Some v) (krestrict SN kl)))
        by (rewrite Forall_forall in HK1'; exact (HK1' _ Hm)).
      assert (HOne : out_conts M c v <> []) by (exact (HNne _ HkSN)).
      unfold mirror_look. simpl.
      apply ax_output.
      eapply ax_trans; [| exact (Houtp c v P Ha)].
      apply ax_ichoice_same_elems;
        [exact HLne | exact HOne | exact HLst | apply out_conts_Static; exact HsM |].
      intro p. exact (Helems (c,Some v) p HkSN).
    + simpl in Hsta. contradiction.
    + exfalso. simpl in Hleaf.
      assert (H1 := summands_nonempty A1). assert (H2 := summands_nonempty A2).
      destruct (summands A1) as [|x1 l1]; [contradiction |].
      destruct (summands A2) as [|x2 l2]; [contradiction |].
      simpl in Hleaf. injection Hleaf as _ Hrest. destruct l1; simpl in Hrest; discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Completeness.                                                        *)

Lemma tbound_mono : forall n m p, n <= m -> tbound n p -> tbound m p.
Proof. intros n m p Hnm H s r Hwt. assert (H2 := H s r Hwt). lia. Qed.

Lemma tbound_zero_no_act : forall p mu q, tbound 0 p -> lts p (ActExt mu) q -> False.
Proof.
  intros p mu q Htb Hlts.
  assert (Hwt : p ⟹[[mu]] q) by (eapply wt_act; [exact Hlts | apply wt_nil]).
  assert (H := Htb [mu] q Hwt). simpl in H. lia.
Qed.

Lemma summand_in_Static : forall N c Q, gStatic N -> (c ? Q) ∈ summands N -> Static Q.
Proof.
  intros N c Q Hs Hin.
  pose proof (summands_gStatic N Hs) as H. rewrite Forall_forall in H.
  assert (Hg := H _ Hin). inversion Hg; subst. assumption.
Qed.

Lemma summand_out_Static : forall N c v Q, gStatic N -> (c ! v • Q) ∈ summands N -> Static Q.
Proof.
  intros N c v Q Hs Hin.
  pose proof (summands_gStatic N Hs) as H. rewrite Forall_forall in H.
  assert (Hg := H _ Hin). inversion Hg; subst. assumption.
Qed.

(** The recursion, on the *semantic* measure [tbound] — a bound on the
    length of the traces the right-hand side can perform.

    A syntactic measure cannot work: normalisation is not
    size-decreasing (the expansion law blows terms up).  A trace bound
    is preserved by [⊑ₘᵤₛₜᵢ] ([tbound_transfer]), hence survives
    normalisation, and drops strictly at every matched summand
    ([tbound_step]).  Inside one bound, the [⊕]-layer is measured by
    [gsize], which is fine because [⊕]-branches are strict subterms and
    need no renormalisation. *)
Theorem completeness_ax_bounded : forall n p q,
  Static p -> Static q -> tbound n q -> p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intro n. induction n as [n IHn] using (well_founded_induction lt_wf).
  intros p q Hp Hq Htb Hpre.
  destruct (full_normalize p Hp) as (M & HsM & HtnfM & HpM & HMp).
  destruct (full_normalize q Hq) as (N & HsN & HtnfN & HqN & HNq).
  assert (HSM : Static (g M)) by (eapply ax_pre_static_preserved; [exact HpM | exact Hp]).
  assert (HSN : Static (g N)) by (eapply ax_pre_static_preserved; [exact HqN | exact Hq]).
  assert (HtbN : tbound n (g N)).
  { eapply tbound_transfer; [exact Hq | exact HSN | | exact Htb].
    apply soundness_ax; assumption. }
  assert (HpreMN : (g M) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N)).
  { transitivity p; [apply soundness_ax; assumption |].
    transitivity q; [exact Hpre | apply soundness_ax; assumption]. }
  eapply ax_trans; [exact HpM |]. eapply ax_trans; [| exact HNq].
  assert (Hstable : forall N' M', gStatic N' -> gStable N' -> Static (g N') ->
      tbound n (g N') -> gStatic M' -> tau_nf M' -> Static (g M') ->
      (g M') ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N') -> ax_pre (g M') (g N')).
  { intros N' M' HsN' HstN' HSN' HtbN' HsM' HtnfM' HSM' Hp'.
    apply ax_stable_step; try assumption.
    - intros c Q HQ v.
      assert (Hlts : lts (g N') ((c ▷ v) ?) (Q ^ v)) by (apply summand_lts_in; exact HQ).
      assert (HSQ : Static (Q ^ v))
        by (apply Static_subst; exact (summand_in_Static N' c Q HsN' HQ)).
      assert (Hne : in_conts M' c <> [])
        by (exact (conts_at_nonempty M' N' (c ? Q) (c, None) HSM' HSN' HtnfM' Hp' HQ eq_refl)).
      assert (HSl : Static ((g (ichoice (in_conts M' c))) ^ v)).
      { apply Static_subst. constructor. apply ichoice_gStatic.
        apply in_conts_Static. exact HsM'. }
      destruct n as [|n'].
      + exfalso. exact (tbound_zero_no_act (g N') _ _ HtbN' Hlts).
      + assert (HtbQ : tbound n' (Q ^ v)).
        { eapply tbound_step;
            [ apply tnf_stable; exact HstN'
            | rewrite (leaves_stable_self N' HstN'); apply elem_of_cons; left; reflexivity
            | exact Hlts | exact HtbN' ]. }
        destruct (in_conts M' c) as [|p0 l] eqn:E; [contradiction |].
        apply (IHn n' (Nat.lt_succ_diag_r n')); try assumption.
        rewrite <- E.
        eapply in_cont_below; [exact HsM' | exact HtnfM' | exact HSQ | exact E
                              | exact HQ | exact Hp'].
    - intros c v Q HQ.
      assert (Hlts : lts (g N') ((c ▷ v) !) Q) by (apply summand_lts_out; exact HQ).
      assert (HSQ : Static Q) by (exact (summand_out_Static N' c v Q HsN' HQ)).
      assert (Hne : out_conts M' c v <> [])
        by (exact (conts_at_nonempty M' N' (c ! v • Q) (c, Some v)
                     HSM' HSN' HtnfM' Hp' HQ eq_refl)).
      assert (HSl : Static (g (ichoice (out_conts M' c v)))).
      { constructor. apply ichoice_gStatic. apply out_conts_Static. exact HsM'. }
      destruct n as [|n'].
      + exfalso. exact (tbound_zero_no_act (g N') _ _ HtbN' Hlts).
      + assert (HtbQ : tbound n' Q).
        { eapply tbound_step;
            [ apply tnf_stable; exact HstN'
            | rewrite (leaves_stable_self N' HstN'); apply elem_of_cons; left; reflexivity
            | exact Hlts | exact HtbN' ]. }
        destruct (out_conts M' c v) as [|p0 l] eqn:E; [contradiction |].
        apply (IHn n' (Nat.lt_succ_diag_r n')); try assumption.
        rewrite <- E.
        eapply out_cont_below; [exact HsM' | exact HtnfM' | exact HSQ | exact E
                               | exact HQ | exact Hp']. }
  assert (Hinner : forall m N', gsize N' <= m -> gStatic N' -> tau_nf N' ->
      Static (g N') -> tbound n (g N') ->
      forall M', gStatic M' -> tau_nf M' -> Static (g M') ->
      (g M') ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N') -> ax_pre (g M') (g N')).
  { induction m as [|m IHm]; intros N' Hsz HsN' HtnfN' HSN' HtbN' M' HsM' HtnfM' HSM' Hp';
      destruct HtnfN' as [Nx HstN' | N1 N2 Ht1 Ht2].
    - apply Hstable; assumption.
    - simpl in Hsz. lia.
    - apply Hstable; assumption.
    - destruct (gStatic_tau_choice N1 N2 HsN') as (Hs1 & Hs2).
      assert (Hl1 : lts (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (g N1))
        by (apply lts_choiceL; apply lts_tau).
      assert (Hl2 : lts (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (g N2))
        by (apply lts_choiceR; apply lts_tau).
      apply ax_int_glb.
      + apply (IHm N1); try assumption.
        * simpl in Hsz. lia.
        * constructor; exact Hs1.
        * eapply tbound_tau; [exact Hl1 | exact HtbN'].
        * transitivity (g ((𝛕 • (g N1)) + (𝛕 • (g N2))));
            [exact Hp' | apply must_i_int_choice_l].
      + apply (IHm N2); try assumption.
        * simpl in Hsz. lia.
        * constructor; exact Hs2.
        * eapply tbound_tau; [exact Hl2 | exact HtbN'].
        * transitivity (g ((𝛕 • (g N1)) + (𝛕 • (g N2))));
            [exact Hp' | apply must_i_int_choice_r]. }
  apply (Hinner (gsize N) N (le_n _)); assumption.
Qed.

(** ** Completeness of [ax_pre] for the [Static] fragment *)
Theorem completeness_ax : forall p q,
  Static p -> Static q -> p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq Hpre.
  eapply completeness_ax_bounded; [exact Hp | exact Hq | | exact Hpre].
  apply Static_tbound. exact Hq.
Qed.

End CompletenessAx.
