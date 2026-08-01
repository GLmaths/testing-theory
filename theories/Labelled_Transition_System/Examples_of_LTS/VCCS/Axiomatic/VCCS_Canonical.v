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

(** * Towards a *canonical* guarded-sum normal form

    [VCCS_NormalForm.v]'s [normal_form] already puts every [Static]
    process into guarded-sum shape [g M]. For [CompletenessAx.v] that is
    not quite enough: the form must additionally be **canonical**, i.e.
    carry *at most one summand per action* (at most one input guard per
    channel, at most one output guard per channel-and-value). See
    [DefinitionAxiomatic.v]'s [ax_input_distrib_l] comment for why
    completeness needs this — in short, [⊑ₘᵤₛₜᵢ] only ever supplies an
    *existential* matching between the two compared processes'
    configurations, never a fixed pairing, and an [ax_pre] derivation has
    to be built from a definite one; collapsing same-action summands
    removes the choice.

    This file builds that construction. The step below is the crux move,
    and it is worth noting what it costs: **nothing** beyond the rules
    already in the system. When the need to rewrite a same-action pair
    sitting *inside* a larger sum was first identified, the fallback plan
    was to add four more [ax_pre] axioms carrying an explicit context
    [R]. With [ax_choice_stable] available
    ([VCCS_ReadySet.v]/[DefinitionAxiomatic.v]) they are instead
    *derivable*, in three lines each — no new axioms, no new [must]
    inductions. The [gStable] side conditions are discharged by
    [simpl; exact I] because an input/output guard is stable by
    definition, and — crucially — [ax_choice_stable] constrains only the
    summand being *rewritten*, never the context [R], so [R] may contain
    [𝛕]-guards freely. That matters: a canonical form generally does
    still have several [𝛕]-summands (they encode genuine internal
    choice and cannot be merged — there is no distributivity law for
    [𝛕], nor should there be), so any collapse step has to tolerate them
    in the context. *)

From Stdlib Require Import List Permutation PeanoNat Lia.
From Stdlib.Wellfounded Require Import Inverse_Image.
From stdpp Require Import base sets gmap.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation WeakTransitions Convergence VCCS_Static VCCS_Precongruence
  VCCS_Expansion VCCS_ResNormalize VCCS_ReadySet DefinitionAxiomatic.
Import ListNotations.

Section VCCS_Canonical.

Context `{VP : VCCS_Parameters}.

(** ** Collapsing a same-action pair underneath an arbitrary context

    [R] is unconstrained — in particular it may contain [𝛕]-guards. *)

Lemma ax_collapse_input_ctx_l : forall c P Q R,
  ax_pre (g ((c ? P) + (c ? Q) + R)) (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R)).
Proof.
  intros c P Q R.
  apply ax_choice_stable.
  - simpl. split; exact I.
  - simpl. exact I.
  - apply ax_input_distrib_l.
Qed.

Lemma ax_collapse_input_ctx_r : forall c P Q R, Static P -> Static Q ->
  ax_pre (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R)) (g ((c ? P) + (c ? Q) + R)).
Proof.
  intros c P Q R HP HQ.
  apply ax_choice_stable.
  - simpl. exact I.
  - simpl. split; exact I.
  - apply ax_input_distrib_r; assumption.
Qed.

Lemma ax_collapse_output_ctx_l : forall c v P Q R,
  ax_pre (g ((c ! v • P) + (c ! v • Q) + R)) (g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + R)).
Proof.
  intros c v P Q R.
  apply ax_choice_stable.
  - simpl. split; exact I.
  - simpl. exact I.
  - apply ax_output_distrib_l.
Qed.

Lemma ax_collapse_output_ctx_r : forall c v P Q R, Static P -> Static Q ->
  ax_pre (g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + R)) (g ((c ! v • P) + (c ! v • Q) + R)).
Proof.
  intros c v P Q R HP HQ.
  apply ax_choice_stable.
  - simpl. exact I.
  - simpl. split; exact I.
  - apply ax_output_distrib_r; assumption.
Qed.

(** ** Flattening a sum into its list of summands

    The collapse steps above act on a same-action pair sitting at the
    *front* of a sum. Reaching that shape from an arbitrary position in
    a [+]-tree is a permutation-modulo-[≡*] problem, which structural
    congruence already answers: [≡*] has both commutativity and
    associativity of [+], so every permutation of a sum's summands is
    reachable. [rebuild] deliberately maps [[]] to [𝟘] and does *not*
    special-case a singleton — [rebuild [a] = a + 𝟘], which [≡*]
    identifies with [a] via [cgr_choice_nil_rev]. That keeps the
    recursion uniform and, usefully, means the "rest" list may always be
    taken to exist (possibly empty) rather than special-casing a
    two-summand sum. *)

Fixpoint summands (M : gproc) : list gproc :=
match M with
| M1 + M2 => summands M1 ++ summands M2
| b => [b]
end.

Fixpoint rebuild (l : list gproc) : gproc :=
match l with
| [] => 𝟘
| a :: l' => a + rebuild l'
end.

Lemma rebuild_app : forall l1 l2, g (rebuild (l1 ++ l2)) ≡* g (rebuild l1 + rebuild l2).
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl.
  - transitivity (g (rebuild l2 + 𝟘)).
    + apply cgr_choice_nil_rev.
    + apply cgr_choice_com.
  - transitivity (g (a + (rebuild l1 + rebuild l2))).
    + apply cgr_fullchoice; [reflexivity | apply IH].
    + apply cgr_choice_assoc_rev.
Qed.

Lemma summands_cgr : forall M, g M ≡* g (rebuild (summands M)).
Proof.
  induction M; simpl; try apply cgr_choice_nil_rev.
  transitivity (g (rebuild (summands M1) + rebuild (summands M2))).
  - apply cgr_fullchoice; assumption.
  - symmetry. apply rebuild_app.
Qed.

Lemma rebuild_perm : forall l l', Permutation l l' -> g (rebuild l) ≡* g (rebuild l').
Proof.
  intros l l' Hp. induction Hp; simpl.
  - reflexivity.
  - apply cgr_fullchoice; [reflexivity | assumption].
  - transitivity (g ((y + x) + rebuild l)).
    + apply cgr_choice_assoc_rev.
    + transitivity (g ((x + y) + rebuild l)).
      * apply cgr_choice; apply cgr_choice_com.
      * apply cgr_choice_assoc.
  - transitivity (g (rebuild l')); assumption.
Qed.

(** Any two summands, wherever they sit, can be brought to the front —
    exactly the shape the four collapse steps consume. *)

Lemma pull_pair : forall M a b l,
  Permutation (summands M) (a :: b :: l) ->
  g M ≡* g ((a + b) + rebuild l).
Proof.
  intros M a b l Hp.
  transitivity (g (rebuild (summands M))); [apply summands_cgr |].
  transitivity (g (rebuild (a :: b :: l))); [apply rebuild_perm; exact Hp |].
  simpl. apply cgr_choice_assoc_rev.
Qed.

(** Elements of [summands M] are themselves leaves — needed whenever
    [summands (rebuild r)] has to be computed for an [r] that came from
    flattening. *)
Lemma summands_leaves : forall M, Forall (fun a => summands a = [a]) (summands M).
Proof.
  induction M; simpl; try (constructor; [reflexivity | constructor]).
  apply Forall_app. split; assumption.
Qed.

(** ** [gStatic] survives flattening, rebuilding and permuting *)

Lemma summands_gStatic : forall M, gStatic M -> Forall gStatic (summands M).
Proof.
  induction M; intro H; simpl; try (constructor; [exact H | constructor]).
  inversion H; subst. apply Forall_app. split; [apply IHM1 | apply IHM2]; assumption.
Qed.

Lemma rebuild_gStatic : forall l, Forall gStatic l -> gStatic (rebuild l).
Proof.
  induction l as [|a l IH]; intro H; simpl.
  - constructor.
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma perm_summands_gStatic : forall M l,
  gStatic M -> Permutation (summands M) l -> Forall gStatic l.
Proof.
  intros M l HM Hp.
  apply Forall_forall. intros x Hx.
  eapply Forall_forall; [apply summands_gStatic; exact HM |].
  (* stdpp registers [Permutation] as a setoid for [∈], so [rewrite] applies. *)
  rewrite Hp. exact Hx.
Qed.

(** ** Collapsing a same-action pair sitting at *arbitrary* positions

    The payoff: given only that two same-action guards occur somewhere
    among [M]'s summands, [⊢] proves [M] equal to the sum with those two
    merged into a single guard. Both directions. Note the [Static] side
    condition of [ax_cgr] is discharged from [gStatic M] alone, via the
    three preservation lemmas above. *)

Theorem ax_collapse_input_anywhere : forall M c P Q l,
  gStatic M ->
  Permutation (summands M) ((c ? P) :: (c ? Q) :: l) ->
  ax_pre (g M) (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild l))
  /\ ax_pre (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild l)) (g M).
Proof.
  intros M c P Q l HM Hp.
  assert (Hall : Forall gStatic ((c ? P) :: (c ? Q) :: l))
    by (eapply perm_summands_gStatic; eassumption).
  inversion Hall as [| ? ? HcP Hall2]; subst.
  inversion Hall2 as [| ? ? HcQ Hall3]; subst.
  inversion HcP; subst. inversion HcQ; subst.
  assert (Hmid : Static (g ((c ? P) + (c ? Q) + rebuild l))).
  { constructor. constructor; [constructor; constructor; assumption |].
    apply rebuild_gStatic. assumption. }
  split.
  - eapply ax_trans.
    + apply ax_cgr; [exact Hmid | apply pull_pair; exact Hp].
    + apply ax_collapse_input_ctx_l.
  - eapply ax_trans with (q := g ((c ? P) + (c ? Q) + rebuild l)).
    + apply ax_collapse_input_ctx_r; assumption.
    + apply ax_cgr_sym; [constructor; exact HM | apply pull_pair; exact Hp].
Qed.

Theorem ax_collapse_output_anywhere : forall M c v P Q l,
  gStatic M ->
  Permutation (summands M) ((c ! v • P) :: (c ! v • Q) :: l) ->
  ax_pre (g M) (g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild l))
  /\ ax_pre (g ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild l)) (g M).
Proof.
  intros M c v P Q l HM Hp.
  assert (Hall : Forall gStatic ((c ! v • P) :: (c ! v • Q) :: l))
    by (eapply perm_summands_gStatic; eassumption).
  inversion Hall as [| ? ? HcP Hall2]; subst.
  inversion Hall2 as [| ? ? HcQ Hall3]; subst.
  inversion HcP; subst. inversion HcQ; subst.
  assert (Hmid : Static (g ((c ! v • P) + (c ! v • Q) + rebuild l))).
  { constructor. constructor; [constructor; constructor; assumption |].
    apply rebuild_gStatic. assumption. }
  split.
  - eapply ax_trans.
    + apply ax_cgr; [exact Hmid | apply pull_pair; exact Hp].
    + apply ax_collapse_output_ctx_l.
  - eapply ax_trans with (q := g ((c ! v • P) + (c ! v • Q) + rebuild l)).
    + apply ax_collapse_output_ctx_r; assumption.
    + apply ax_cgr_sym; [constructor; exact HM | apply pull_pair; exact Hp].
Qed.

(** ** Locating a same-action pair

    [gact] is the *action* a guard offers, at the granularity that
    matters for canonicity: a channel for an input, a channel *and* a
    value for an output, and nothing at all for [①]/[𝟘]/[𝛕] (those can
    never be merged — see the [𝛕] remark at the end of this file).

    [find_dup] returns the two same-action guards *together with the
    remaining summands*. That signature is the point: the function
    thereby supplies exactly the [Permutation] witness that
    [ax_collapse_input_anywhere]/[ax_collapse_output_anywhere] consume,
    so no separate search-correctness plumbing is needed. *)

Definition gact (a : gproc) : option (ChannelData * option ValueData) :=
match a with
| c ? _ => Some (c, None)
| c ! v • _ => Some (c, Some v)
| _ => None
end.

Definition same_act (a b : gproc) : Prop :=
  exists k, gact a = Some k /\ gact b = Some k.

Fixpoint pick_act (k : ChannelData * option ValueData) (l : list gproc)
  : option (gproc * list gproc) :=
match l with
| [] => None
| a :: l' => if decide (gact a = Some k) then Some (a, l')
             else match pick_act k l' with
                  | Some (b, r) => Some (b, a :: r)
                  | None => None
                  end
end.

Lemma pick_act_spec : forall k l b r,
  pick_act k l = Some (b, r) -> gact b = Some k /\ Permutation l (b :: r).
Proof.
  induction l as [|a l IH]; intros b r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct (decide (gact a = Some k)) as [Hd|Hd].
    + injection Heq as H1 H2. subst. split; [exact Hd | reflexivity].
    + destruct (pick_act k l) as [(b0, r0)|] eqn:E; [| discriminate Heq].
      destruct (IH b0 r0 eq_refl) as (Hg & Hp).
      injection Heq as H1 H2. subst.
      split; [exact Hg |].
      transitivity (a :: b :: r0).
      * apply perm_skip. exact Hp.
      * apply perm_swap.
Qed.

Lemma perm_move2 : forall (a x y : gproc) r, Permutation (a::x::y::r) (x::y::a::r).
Proof.
  intros. transitivity (x::a::y::r).
  - apply perm_swap.
  - apply perm_skip. apply perm_swap.
Qed.

Fixpoint find_dup (l : list gproc) : option (gproc * gproc * list gproc) :=
match l with
| [] => None
| a :: l' =>
    match gact a with
    | Some k =>
        match pick_act k l' with
        | Some (b, r) => Some (a, b, r)
        | None => match find_dup l' with
                  | Some (x, y, r) => Some (x, y, a :: r)
                  | None => None
                  end
        end
    | None => match find_dup l' with
              | Some (x, y, r) => Some (x, y, a :: r)
              | None => None
              end
    end
end.

Lemma find_dup_spec : forall l a b r,
  find_dup l = Some (a, b, r) -> same_act a b /\ Permutation l (a :: b :: r).
Proof.
  induction l as [|a0 l IH]; intros a b r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct (gact a0) as [k|] eqn:Ek.
    + destruct (pick_act k l) as [(b0, r0)|] eqn:E2.
      * injection Heq as H1 H2 H3. subst.
        destruct (pick_act_spec k l b r E2) as (Hg & Hp).
        split.
        -- exists k. split; [exact Ek | exact Hg].
        -- apply perm_skip. exact Hp.
      * destruct (find_dup l) as [((x,y),r1)|] eqn:E3; [| discriminate Heq].
        destruct (IH x y r1 eq_refl) as (Hs & Hp).
        injection Heq as H1 H2 H3. subst.
        split; [exact Hs |].
        transitivity (a0 :: a :: b :: r1).
        -- apply perm_skip. exact Hp.
        -- apply perm_move2.
    + destruct (find_dup l) as [((x,y),r1)|] eqn:E3; [| discriminate Heq].
      destruct (IH x y r1 eq_refl) as (Hs & Hp).
      injection Heq as H1 H2 H3. subst.
      split; [exact Hs |].
      transitivity (a0 :: a :: b :: r1).
      * apply perm_skip. exact Hp.
      * apply perm_move2.
Qed.

(** ** When the search fails, the sum really is canonical

    [count_act k l] counts the summands offering action [k], and
    [find_dup_none_count] is the "stop" half of the driver: once
    [find_dup] returns [None], every action occurs at most once.

    **This is deliberately phrased over summands, not over LTS labels.**
    An earlier draft stated canonicity as "unique continuation per
    action" ([g M ⟶[μ] p1 -> g M ⟶[μ] p2 -> p1 = p2]). That statement
    happens to be true — [μ] for an input is [(c,v)?] and so already
    carries the value, which pins the target [P^v] — but it is the wrong
    *shape* to consume: an input's continuation is a value-indexed
    *family*, and [ax_input] is the omega rule [(∀v, ⊢ p^v ⊑ q^v) ->
    ⊢ g (c?p) ⊑ g (c?q)]. Per-[μ] uniqueness would yield separate facts
    about each [P^v] with no way to reassemble them into the [∀v] family
    [ax_input] requires. Counting summands instead gives
    [CompletenessAx.v] a single matched input *summand*, from which the
    [∀v] family follows directly. (Credit where due: this was caught by
    the user, pointing at an input followed by an output depending on the
    received value.) *)

Fixpoint count_act (k : ChannelData * option ValueData) (l : list gproc) : nat :=
match l with
| [] => 0
| a :: l' => if decide (gact a = Some k) then S (count_act k l') else count_act k l'
end.

Lemma pick_act_none_count : forall k l, pick_act k l = None -> count_act k l = 0.
Proof.
  induction l as [|a l IH]; intro Heq; simpl in *.
  - reflexivity.
  - destruct (decide (gact a = Some k)) as [Hd|Hd].
    + discriminate Heq.
    + apply IH. destruct (pick_act k l) as [(b,r)|]; [discriminate Heq | reflexivity].
Qed.

Lemma find_dup_none_count : forall l, find_dup l = None -> forall k, count_act k l <= 1.
Proof.
  induction l as [|a l IH]; intro Heq; intro k; simpl in *.
  - apply Nat.le_0_l.
  - destruct (gact a) as [k0|] eqn:Ek.
    + destruct (pick_act k0 l) as [(b,r)|] eqn:E2; [discriminate Heq |].
      destruct (find_dup l) as [((x,y),r1)|] eqn:E3; [discriminate Heq |].
      destruct (decide (Some k0 = Some k)) as [He|He].
      * injection He as He. subst k0.
        rewrite (pick_act_none_count k l E2). apply Nat.le_refl.
      * apply IH; reflexivity.
    + destruct (find_dup l) as [((x,y),r1)|] eqn:E3; [discriminate Heq |].
      destruct (decide (@None (ChannelData * option ValueData) = Some k)) as [He|He].
      * discriminate He.
      * apply IH; reflexivity.
Qed.

Definition canonical (M : gproc) : Prop := find_dup (summands M) = None.

Lemma canonical_count : forall M, canonical M -> forall k, count_act k (summands M) <= 1.
Proof. intros M H k. apply find_dup_none_count. exact H. Qed.

(** ** Selecting a [𝛕]-summand

    The same search/rebuild pattern as [find_dup], but aimed at the
    *next* normalisation stage — reaching an internal choice of stable
    sums. [find_tau] locates a [𝛕]-guarded summand and returns its
    continuation together with the remaining summands, so
    [find_tau_spec]'s [Permutation] feeds [pull_one] directly, producing
    exactly the shape [ax_tau_sep_l]/[ax_tau_flatten_l] consume
    ([DefinitionAxiomatic.v]).

    [pull_one] is the one-summand analogue of [pull_pair], and simpler:
    no re-association is needed, since [rebuild (a :: r)] *is*
    [a + rebuild r] definitionally. *)

Lemma pull_one : forall M a r,
  Permutation (summands M) (a :: r) -> g M ≡* g (a + rebuild r).
Proof.
  intros M a r Hp.
  transitivity (g (rebuild (summands M))); [apply summands_cgr |].
  apply (rebuild_perm (summands M) (a :: r)). exact Hp.
Qed.

Fixpoint find_tau (l : list gproc) : option (proc * list gproc) :=
match l with
| [] => None
| a :: l' =>
    match a with
    | 𝛕 • p => Some (p, l')
    | _ => match find_tau l' with
           | Some (p, r) => Some (p, a :: r)
           | None => None
           end
    end
end.

Lemma find_tau_spec : forall l p r,
  find_tau l = Some (p, r) -> Permutation l ((𝛕 • p) :: r).
Proof.
  induction l as [|a l IH]; intros p r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct a as [ | | c p1 | c v p1 | p1 | N1 N2 ];
      try (destruct (find_tau l) as [(p0,r0)|] eqn:E; [| discriminate Heq];
           injection Heq as H1 H2; subst;
           etransitivity; [apply perm_skip; apply IH; reflexivity | apply perm_swap]).
    injection Heq as H1 H2. subst. reflexivity.
Qed.

Lemma find_tau_app_none : forall l1 l2,
  find_tau (l1 ++ l2) = None -> find_tau l1 = None /\ find_tau l2 = None.
Proof.
  induction l1 as [|a l1 IH]; intros l2 H; simpl in *.
  - split; [reflexivity | exact H].
  - destruct a as [ | | c p1 | c v p1 | p1 | N1 N2 ];
      try (destruct (find_tau (l1 ++ l2)) as [(p0,r0)|] eqn:E; [discriminate H |];
           destruct (IH l2 E) as (H1 & H2);
           rewrite H1; split; [reflexivity | exact H2]).
    discriminate H.
Qed.

(** The "stop" side: no [𝛕]-summand anywhere means the sum is stable. *)
Lemma find_tau_none_stable : forall M, find_tau (summands M) = None -> gStable M.
Proof.
  induction M; intro H; simpl in *; try exact I.
  - discriminate H.
  - destruct (find_tau_app_none _ _ H) as (H1 & H2).
    split; [apply IHM1 | apply IHM2]; assumption.
Qed.

(** ** The two [𝛕]-normalisation steps, at arbitrary positions

    Both follow the pattern of [ax_collapse_*_anywhere] above: bring the
    chosen summand to the front with [pull_one], commute it to the *end*
    (both laws are stated with the [𝛕]-summand rightmost), then apply
    the law. [ax_cgr]'s [Static] side condition is discharged from
    [gStatic M] alone, via [tau_mid_static]. *)

Lemma tau_pull_cgr : forall M Y r,
  Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  g M ≡* g (rebuild r + (𝛕 • (g Y))).
Proof.
  intros M Y r Hp.
  transitivity (g ((𝛕 • (g Y)) + rebuild r)).
  - apply pull_one. exact Hp.
  - apply cgr_choice_com.
Qed.

Lemma tau_mid_static : forall M Y r,
  gStatic M -> Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  gStatic Y /\ Forall gStatic r /\ Static (g (rebuild r + (𝛕 • (g Y)))).
Proof.
  intros M Y r HM Hp.
  assert (Hall : Forall gStatic ((𝛕 • (g Y)) :: r))
    by (eapply perm_summands_gStatic; eassumption).
  inversion Hall as [| ? ? Htau Hrest]; subst.
  inversion Htau; subst. inversion H0; subst.
  repeat split; [assumption | assumption |].
  constructor. constructor.
  - apply rebuild_gStatic. assumption.
  - constructor. constructor. assumption.
Qed.

Theorem ax_tau_sep_anywhere : forall M Y r,
  gStatic M ->
  Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  ax_pre (g M) (g ((𝛕 • (g (rebuild r + Y))) + (𝛕 • (g Y))))
  /\ ax_pre (g ((𝛕 • (g (rebuild r + Y))) + (𝛕 • (g Y)))) (g M).
Proof.
  intros M Y r HM Hp.
  destruct (tau_mid_static M Y r HM Hp) as (HY & Hr & Hmid).
  split.
  - eapply ax_trans.
    + apply ax_cgr; [exact Hmid | apply tau_pull_cgr; exact Hp].
    + apply ax_tau_sep_l.
  - eapply ax_trans with (q := g (rebuild r + (𝛕 • (g Y)))).
    + apply ax_tau_sep_r.
    + apply ax_cgr_sym; [constructor; exact HM | apply tau_pull_cgr; exact Hp].
Qed.

Theorem ax_tau_flatten_anywhere : forall M Y r,
  gStatic M -> gAllTau Y ->
  Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  ax_pre (g M) (g (rebuild r + Y)) /\ ax_pre (g (rebuild r + Y)) (g M).
Proof.
  intros M Y r HM HAT Hp.
  destruct (tau_mid_static M Y r HM Hp) as (HY & Hr & Hmid).
  split.
  - eapply ax_trans.
    + apply ax_cgr; [exact Hmid | apply tau_pull_cgr; exact Hp].
    + apply ax_tau_flatten_l. exact HAT.
  - eapply ax_trans with (q := g (rebuild r + (𝛕 • (g Y)))).
    + apply ax_tau_flatten_r. exact HAT.
    + apply ax_cgr_sym; [constructor; exact HM | apply tau_pull_cgr; exact Hp].
Qed.

(** ** The target shape

    [tau_nf] is Hennessy's [⊕]-of-stable-sums, as a binary tree of
    internal choices with [gStable] leaves — exactly the shape
    [ax_tau_sep_anywhere] produces at each step. Its two cases are also
    precisely the dichotomy the normalisation recursion dispatches on:
    a [𝛕]-continuation in [tau_nf] is either already stable (nothing to
    do) or is [gAllTau] (so [ax_tau_flatten_anywhere] applies). *)

Inductive tau_nf : gproc -> Prop :=
| tnf_stable : forall M, gStable M -> tau_nf M
| tnf_choice : forall M1 M2, tau_nf M1 -> tau_nf M2 ->
    tau_nf ((𝛕 • (g M1)) + (𝛕 • (g M2))).

Lemma tau_nf_gAllTau_or_stable : forall M, tau_nf M -> gStable M \/ gAllTau M.
Proof.
  intros M H. destruct H.
  - left. exact H.
  - right. simpl. split; exact I.
Qed.

(** ** The separation recursion

    Measure: [ntaus], the number of [𝛕]-summands. Each application of
    [ax_tau_sep_anywhere] peels one off and recurses into
    [rebuild r + Y]; since the invariant [tau_cont_ok] guarantees the
    peeled continuation [Y] is *stable*, [Y] contributes no [𝛕]-summands
    of its own and the measure strictly decreases. (This is exactly what
    [ax_tau_flatten_*] is for — establishing that invariant. Without it
    [Y] could be a nested internal choice and the count would grow.) *)

Fixpoint ntaus (l : list gproc) : nat :=
match l with
| [] => 0
| a :: l' => match a with 𝛕 • _ => S (ntaus l') | _ => ntaus l' end
end.

Lemma ntaus_app : forall l1 l2, ntaus (l1 ++ l2) = (ntaus l1 + ntaus l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl.
  - reflexivity.
  - destruct a; rewrite IH; reflexivity.
Qed.

Lemma ntaus_perm : forall l l', Permutation l l' -> ntaus l = ntaus l'.
Proof.
  intros l l' Hp. induction Hp; simpl.
  - reflexivity.
  - destruct x; rewrite IHHp; reflexivity.
  - destruct y; destruct x; reflexivity.
  - rewrite IHHp1. exact IHHp2.
Qed.

Lemma ntaus_summands_rebuild : forall l,
  Forall (fun a => summands a = [a]) l -> ntaus (summands (rebuild l)) = ntaus l.
Proof.
  induction l as [|a l IH]; intro Hall; simpl.
  - reflexivity.
  - inversion Hall as [|? ? Ha Hall']; subst.
    rewrite ntaus_app. rewrite Ha. simpl.
    destruct a; rewrite (IH Hall'); reflexivity.
Qed.

Lemma gStable_ntaus_zero : forall Y, gStable Y -> ntaus (summands Y) = 0.
Proof.
  induction Y; intro H; simpl in *; try reflexivity.
  - contradiction.
  - destruct H as (H1 & H2). rewrite ntaus_app.
    rewrite (IHY1 H1). rewrite (IHY2 H2). reflexivity.
Qed.

(** The invariant the recursion maintains: every [𝛕]-summand's
    continuation is a *stable* guarded sum. *)

Definition tau_cont_ok (a : gproc) : Prop :=
match a with
| 𝛕 • p => exists Y, p = g Y /\ gStable Y
| _ => True
end.

Lemma tau_cont_ok_perm : forall l l', Permutation l l' ->
  Forall tau_cont_ok l -> Forall tau_cont_ok l'.
Proof.
  intros l l' Hp Hall.
  apply Forall_forall. intros x Hx.
  rewrite Forall_forall in Hall. apply Hall. rewrite Hp. exact Hx.
Qed.

Lemma tau_cont_ok_stable : forall Y, gStable Y -> Forall tau_cont_ok (summands Y).
Proof.
  induction Y; intro H; simpl in *; try (constructor; [exact I | constructor]).
  - contradiction.
  - destruct H as (H1 & H2). apply Forall_app. split; [apply IHY1 | apply IHY2]; assumption.
Qed.

Lemma tau_cont_ok_rebuild : forall l, Forall (fun a => summands a = [a]) l ->
  Forall tau_cont_ok l -> Forall tau_cont_ok (summands (rebuild l)).
Proof.
  induction l as [|a l IH]; intros Hlv Hall; simpl.
  - constructor; [exact I | constructor].
  - inversion Hlv as [|? ? Ha Hlv']; subst.
    inversion Hall as [|? ? Hok Hall']; subst.
    apply Forall_app. rewrite Ha. split.
    + constructor; [exact Hok | constructor].
    + apply IH; assumption.
Qed.

(** ** Rewriting a [𝛕]-summand's continuation in place

    Unlike the separation/flattening steps, this one needs no
    commutation: [ax_choice_tau] already expects the [𝛕]-summand
    *leftmost*, which is exactly where [pull_one] puts it. *)

Lemma tau_cont_mid_static : forall M q r,
  gStatic M -> Permutation (summands M) ((𝛕 • q) :: r) ->
  Static q /\ Forall gStatic r /\ Static (g ((𝛕 • q) + rebuild r)).
Proof.
  intros M q r HM Hp.
  assert (Hall : Forall gStatic ((𝛕 • q) :: r))
    by (eapply perm_summands_gStatic; eassumption).
  inversion Hall as [| ? ? Htau Hrest]; subst.
  inversion Htau; subst.
  repeat split; [assumption | assumption |].
  constructor. constructor.
  - constructor. assumption.
  - apply rebuild_gStatic. assumption.
Qed.

Theorem ax_tau_cont_anywhere : forall M q q' r,
  gStatic M -> Static q' ->
  Permutation (summands M) ((𝛕 • q) :: r) ->
  ax_pre q q' -> ax_pre q' q ->
  ax_pre (g M) (g ((𝛕 • q') + rebuild r))
  /\ ax_pre (g ((𝛕 • q') + rebuild r)) (g M).
Proof.
  intros M q q' r HM Hq' Hp Hf Hb.
  destruct (tau_cont_mid_static M q r HM Hp) as (Hqst & Hrst & Hmid).
  split.
  - eapply ax_trans.
    + apply ax_cgr; [exact Hmid | apply pull_one; exact Hp].
    + apply ax_choice_tau. exact Hf.
  - eapply ax_trans with (q := g ((𝛕 • q) + rebuild r)).
    + apply ax_choice_tau. exact Hb.
    + apply ax_cgr_sym; [constructor; exact HM | apply pull_one; exact Hp].
Qed.

(** ** Turning a [𝛕]-summand into a strictly smaller process

    The payoff of [VCCS_NormalForm.v]'s [step_dominated]. A [𝛕]-summand
    of the normal form is a [τ]-transition of it, hence matched by a
    [τ]-transition of the *original* [p]; the matched target is a genuine
    reduct of [p], so `Static_lts_decrease` makes it strictly smaller in
    [size] and the caller can recurse on it, transporting the result back
    along the [⊢]-equality. This is what lets the normalisation descend
    into continuations despite normalisation not being size-decreasing. *)

(** Defined here rather than in [VCCS_NormalForm.v] (where
    [normal_form_strong] establishes it) purely for dependency order:
    [VCCS_NormalForm.v] imports this file. *)
Definition step_dominated (p : proc) (M : gproc) : Prop :=
  forall a q, lts (g M) a q -> exists r, lts p a r /\ ax_pre q r /\ ax_pre r q.

Lemma summand_lts_tau : forall M q, (𝛕 • q) ∈ summands M -> lts (g M) τ q.
Proof.
  induction M; intros q Hin; simpl in Hin.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - assert (Heq : (𝛕 • q) = (𝛕 • p)) by set_solver.
    injection Heq as Heq. subst. apply lts_tau.
  - apply elem_of_app in Hin. destruct Hin as [H|H].
    + apply lts_choiceL. apply IHM1. exact H.
    + apply lts_choiceR. apply IHM2. exact H.
Qed.

Lemma tau_summand_reduct : forall p M q r,
  Static p -> gStatic M -> step_dominated p M ->
  Permutation (summands M) ((𝛕 • q) :: r) ->
  exists u, ax_pre q u /\ ax_pre u q /\ Static u /\ (size u < size p)%nat.
Proof.
  intros p M q r Hp HM Hd Hperm.
  assert (Hin : (𝛕 • q) ∈ summands M) by (rewrite Hperm; left).
  destruct (Hd τ q (summand_lts_tau M q Hin)) as (u & Hlu & Hqu & Huq).
  exists u. repeat split; [exact Hqu | exact Huq | | ].
  - eapply Static_preserved_by_lts; eassumption.
  - eapply Static_lts_decrease; eassumption.
Qed.

(** ** Invariant and measure for the flattening phase

    The phase that *establishes* [tau_cont_ok] (which [tau_separate]
    below then consumes). Its own invariant is the weaker
    [tau_cont_nf]: every [𝛕]-summand's continuation is a guarded sum
    already in [tau_nf] — i.e. stable *or* a nested internal choice.
    Flattening removes the second possibility.

    Measure: [tau_weight], the total [size] of the [𝛕]-continuations.
    Each [ax_tau_flatten_anywhere] replaces a summand [𝛕•(g Y)] (with
    [Y = 𝛕•(g A) + 𝛕•(g B)]) by [𝛕•(g A) + 𝛕•(g B)], so one contribution
    of [size (g Y)] becomes [size (g A) + size (g B)], which is strictly
    smaller — the two [𝛕] guards themselves are dropped.

    Note this cannot be merged into [tau_separate]'s recursion with a
    lexicographic measure: separation *increases* [tau_weight] (its new
    continuation [rebuild r + Y] can be large), so the two phases have
    to be sequenced, flattening first. *)

Definition tau_cont_nf (a : gproc) : Prop :=
match a with
| 𝛕 • p => exists Y, p = g Y /\ tau_nf Y
| _ => True
end.

Fixpoint tau_weight (l : list gproc) : nat :=
match l with
| [] => 0
| a :: l' => match a with 𝛕 • p => (size p + tau_weight l')%nat | _ => tau_weight l' end
end.

Lemma tau_weight_app : forall l1 l2,
  tau_weight (l1 ++ l2) = (tau_weight l1 + tau_weight l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl.
  - reflexivity.
  - destruct a; rewrite IH; lia.
Qed.

Lemma tau_weight_perm : forall l l', Permutation l l' -> tau_weight l = tau_weight l'.
Proof.
  intros l l' Hp. induction Hp; simpl.
  - reflexivity.
  - destruct x; lia.
  - destruct y; destruct x; lia.
  - lia.
Qed.

Lemma tau_cont_nf_perm : forall l l', Permutation l l' ->
  Forall tau_cont_nf l -> Forall tau_cont_nf l'.
Proof.
  intros l l' Hp Hall.
  apply Forall_forall. intros x Hx.
  rewrite Forall_forall in Hall. apply Hall. rewrite Hp. exact Hx.
Qed.

(** ** Searching for a [𝛕]-summand still to be flattened

    [gStable] is a [Fixpoint] into [Prop], so it needs a boolean twin to
    be usable as a test inside the search. [find_unstable_tau] then
    returns a [𝛕]-summand whose continuation is a guarded sum that is
    *not* stable, together with the remaining summands — again in
    exactly the [Permutation] shape [ax_tau_flatten_anywhere] consumes.

    Note the search pattern-matches on [𝛕 • (g Y)]: a [𝛕]-summand whose
    continuation is not syntactically a guarded sum is simply skipped.
    That is harmless, because the [tau_cont_nf] invariant rules such
    summands out — and [find_unstable_tau_none] is where that invariant
    is actually cashed in, upgrading [tau_cont_nf] to [tau_cont_ok]. *)

Fixpoint gStableB (M : gproc) : bool :=
match M with
| 𝛕 • _ => false
| M1 + M2 => andb (gStableB M1) (gStableB M2)
| _ => true
end.

Lemma gStableB_spec : forall M, gStableB M = true <-> gStable M.
Proof.
  induction M; simpl; try (split; [intros _; exact I | intros _; reflexivity]).
  - split; [discriminate | contradiction].
  - rewrite Bool.andb_true_iff. rewrite IHM1. rewrite IHM2. reflexivity.
Qed.

Fixpoint find_unstable_tau (l : list gproc) : option (gproc * list gproc) :=
match l with
| [] => None
| a :: l' =>
    match a with
    | 𝛕 • (g Y) =>
        if gStableB Y
        then match find_unstable_tau l' with
             | Some (Z, r) => Some (Z, a :: r)
             | None => None
             end
        else Some (Y, l')
    | _ => match find_unstable_tau l' with
           | Some (Z, r) => Some (Z, a :: r)
           | None => None
           end
    end
end.

Lemma find_unstable_tau_spec : forall l Y r,
  find_unstable_tau l = Some (Y, r) ->
  Permutation l ((𝛕 • (g Y)) :: r) /\ gStableB Y = false.
Proof.
  induction l as [|a l IH]; intros Y r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct a as [ | | c p1 | c v p1 | p1 | N1 N2 ];
      try (destruct (find_unstable_tau l) as [(Z0,r0)|] eqn:E; [| discriminate Heq];
           injection Heq as H1 H2; subst;
           destruct (IH Y r0 eq_refl) as (Hperm & Hst);
           split; [etransitivity; [apply perm_skip; exact Hperm | apply perm_swap] | exact Hst]).
    destruct p1 as [ | | | | | Y0 ];
      try (destruct (find_unstable_tau l) as [(Z0,r0)|] eqn:E; [| discriminate Heq];
           injection Heq as H1 H2; subst;
           destruct (IH Y r0 eq_refl) as (Hperm & Hst);
           split; [etransitivity; [apply perm_skip; exact Hperm | apply perm_swap] | exact Hst]).
    destruct (gStableB Y0) eqn:Est.
    + destruct (find_unstable_tau l) as [(Z0,r0)|] eqn:E; [| discriminate Heq].
      injection Heq as H1 H2; subst.
      destruct (IH Y r0 eq_refl) as (Hperm & Hst).
      split; [etransitivity; [apply perm_skip; exact Hperm | apply perm_swap] | exact Hst].
    + injection Heq as H1 H2. subst. split; [reflexivity | exact Est].
Qed.

Lemma find_unstable_tau_none : forall l,
  find_unstable_tau l = None -> Forall tau_cont_nf l -> Forall tau_cont_ok l.
Proof.
  induction l as [|a l IH]; intros Heq Hall; simpl in Heq.
  - constructor.
  - inversion Hall as [|? ? Ha Hall']; subst.
    destruct a as [ | | c p1 | c v p1 | p1 | N1 N2 ];
      try (destruct (find_unstable_tau l) as [(Z0,r0)|] eqn:E; [discriminate Heq |];
           constructor; [exact I | apply IH; [reflexivity | exact Hall']]).
    destruct Ha as (Y0 & HpY & HnfY). subst p1.
    destruct (gStableB Y0) eqn:Est; [| discriminate Heq].
    destruct (find_unstable_tau l) as [(Z0,r0)|] eqn:E; [discriminate Heq |].
    constructor.
    + exists Y0. split; [reflexivity | apply gStableB_spec; exact Est].
    + apply IH; [reflexivity | exact Hall'].
Qed.

(** ** Deciding [tau_nf]

    Stage 1's search needs to tell whether a [𝛕]-summand's continuation
    is *already* normalised — without it the search re-selects the
    summand it has just rewritten and the recursion makes no progress.
    [tau_nf] is structurally decidable, and the nested recursion below
    (on [A]/[B], which sit two constructors deep under the
    [(𝛕 • (g A)) + (𝛕 • (g B))] pattern) is accepted by the guard
    checker.

    Both directions of the spec are needed: soundness feeds stage 2's
    [tau_cont_nf] invariant, completeness is what stops the search
    re-selecting. The proof runs by well-founded recursion on [gsize]
    rather than plain structural induction, because the interesting
    sub-terms [A], [B] are *not* immediate sub-terms of the argument. *)

Fixpoint tau_nfB (M : gproc) : bool :=
  orb (gStableB M)
      (match M with
       | (𝛕 • (g A)) + (𝛕 • (g B)) => andb (tau_nfB A) (tau_nfB B)
       | _ => false
       end).

Lemma tau_nfB_spec : forall M, tau_nfB M = true <-> tau_nf M.
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  split.
  - intro H.
    destruct (gStableB M) eqn:E.
    + apply tnf_stable. apply gStableB_spec. exact E.
    + destruct M; simpl in H, E; try discriminate H; try discriminate E.
      rewrite E in H. simpl in H.
      destruct M1; try discriminate H.
      destruct p; try discriminate H.
      destruct M2; try discriminate H.
      destruct p; try discriminate H.
      apply Bool.andb_true_iff in H as (H1 & H2).
      apply tnf_choice.
      * apply IH; [simpl; lia | exact H1].
      * apply IH; [simpl; lia | exact H2].
  - intro H. inversion H as [? Hs | A B HA HB]; subst.
    + apply gStableB_spec in Hs.
      destruct M; simpl in *; try reflexivity; try discriminate Hs;
        rewrite Hs; reflexivity.
    + simpl. apply Bool.andb_true_iff. split.
      * apply IH; [simpl; lia | exact HA].
      * apply IH; [simpl; lia | exact HB].
Qed.

(** ** Stage 1's search: a [𝛕]-summand still to be normalised

    Selects a [𝛕]-summand whose continuation is *not* already a guarded
    sum in [tau_nf]. Thanks to [tau_nfB] this is decidable, which is
    what makes the recursion progress: after
    [ax_tau_cont_anywhere] rewrites the continuation to some [g Y] with
    [tau_nf Y], the summand is no longer selectable, so the measure
    [ntodo] strictly drops.

    [todo1]/[ntodo] are deliberately factored through a per-summand
    weight: with the weight isolated, [ntodo_app] and [ntodo_perm] are
    one-liners (`simpl; lia`), whereas inlining the match into the
    [Fixpoint] forces a painful case analysis in the `perm_swap` case. *)

Definition tau_todo (a : gproc) : Prop :=
match a with
| 𝛕 • (g Y) => tau_nfB Y = false
| 𝛕 • _ => True
| _ => False
end.

Definition todo1 (a : gproc) : nat :=
match a with
| 𝛕 • (g Y) => if tau_nfB Y then 0 else 1
| 𝛕 • _ => 1
| _ => 0
end.

Fixpoint ntodo (l : list gproc) : nat :=
match l with
| [] => 0
| a :: l' => (todo1 a + ntodo l')%nat
end.

Lemma ntodo_app : forall l1 l2, ntodo (l1 ++ l2) = (ntodo l1 + ntodo l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl; [reflexivity | rewrite IH; lia].
Qed.

Lemma ntodo_perm : forall l l', Permutation l l' -> ntodo l = ntodo l'.
Proof.
  intros l l' Hp. induction Hp; simpl; lia.
Qed.

Lemma todo1_pos : forall a, tau_todo a -> todo1 a = 1.
Proof.
  intros a H. destruct a as [ | | c pa | c v pa | pa | N1 N2 ]; simpl in *; try contradiction.
  destruct pa; try reflexivity.
  simpl in H. rewrite H. reflexivity.
Qed.

Fixpoint find_tau_todo (l : list gproc) : option (proc * list gproc) :=
match l with
| [] => None
| a :: l' =>
    match a with
    | 𝛕 • (g Y) =>
        if tau_nfB Y
        then match find_tau_todo l' with
             | Some (q, r) => Some (q, a :: r)
             | None => None
             end
        else Some (g Y, l')
    | 𝛕 • q => Some (q, l')
    | _ => match find_tau_todo l' with
           | Some (q, r) => Some (q, a :: r)
           | None => None
           end
    end
end.

Lemma find_tau_todo_spec : forall l q r,
  find_tau_todo l = Some (q, r) ->
  Permutation l ((𝛕 • q) :: r) /\ tau_todo (𝛕 • q).
Proof.
  induction l as [|a l IH]; intros q r Heq; simpl in Heq.
  - discriminate Heq.
  - destruct a as [ | | c pa | c v pa | pa | N1 N2 ];
      try (destruct (find_tau_todo l) as [(q0,r0)|] eqn:E; [| discriminate Heq];
           injection Heq as H1 H2; subst;
           destruct (IH q r0 eq_refl) as (Hperm & Htd);
           split; [etransitivity; [apply perm_skip; exact Hperm | apply perm_swap] | exact Htd]).
    destruct pa as [ pb pc | n | n pb | e pb pc | pb | Y ];
      try (injection Heq as H1 H2; subst; split; [reflexivity | exact I]).
    destruct (tau_nfB Y) eqn:Enf.
    + destruct (find_tau_todo l) as [(q0,r0)|] eqn:E; [| discriminate Heq].
      injection Heq as H1 H2; subst.
      destruct (IH q r0 eq_refl) as (Hperm & Htd).
      split; [etransitivity; [apply perm_skip; exact Hperm | apply perm_swap] | exact Htd].
    + injection Heq as H1 H2. subst. split; [reflexivity | exact Enf].
Qed.

Lemma find_tau_todo_none : forall l,
  find_tau_todo l = None -> Forall tau_cont_nf l.
Proof.
  induction l as [|a l IH]; intro Heq; simpl in Heq.
  - constructor.
  - destruct a as [ | | c pa | c v pa | pa | N1 N2 ];
      try (destruct (find_tau_todo l) as [(q0,r0)|] eqn:E; [discriminate Heq |];
           constructor; [exact I | apply IH; reflexivity]).
    destruct pa as [ pb pc | n | n pb | e pb pc | pb | Y ]; try discriminate Heq.
    destruct (tau_nfB Y) eqn:Enf; [| discriminate Heq].
    destruct (find_tau_todo l) as [(q0,r0)|] eqn:E; [discriminate Heq |].
    constructor.
    + exists Y. split; [reflexivity | apply tau_nfB_spec; exact Enf].
    + apply IH; reflexivity.
Qed.

(** *** External choice lies above internal choice — derived, not an axiom

    [g A ⊕ g B ⊑ g (A + B)]: the union-closure condition acceptance-tree
    semantics imposes on acceptance families (the family must contain
    [ready A ∪ ready B] whenever it contains [ready A] and [ready B]).
    It needs no rule of its own — two applications of [ax_tau_sep_l],
    each followed by [ax_int_l], strip one [𝛕] at a time:

      [𝛕A + 𝛕B]  ⊑  [𝛕(𝛕A + B) + 𝛕B]  ⊑  [𝛕A + B]  ≡  [B + 𝛕A]
                 ⊑  [𝛕(B + A) + 𝛕A]   ⊑  [B + A]   ≡  [A + B]

    The companion *convex*-closure condition is genuinely independent
    and is [DefinitionAxiomatic.v]'s [ax_convex]; between them the two
    conditions are what make an acceptance family saturated, which is
    what the completeness proof consumes. *)

Lemma ax_int_below_ext : forall (A B : gproc), gStatic A -> gStatic B ->
  ax_pre (g ((𝛕 • (g A)) + (𝛕 • (g B)))) (g (A + B)).
Proof.
  intros A B HA HB.
  eapply ax_trans; [apply (ax_tau_sep_l (𝛕 • (g A)) B) |].
  eapply ax_trans; [apply ax_int_l |].
  eapply ax_trans;
    [apply ax_cgr with (q := g (B + (𝛕 • (g A))));
       [constructor; constructor; [exact HB | constructor; constructor; exact HA]
       | apply cgr_choice_com] |].
  eapply ax_trans; [apply (ax_tau_sep_l B A) |].
  eapply ax_trans; [apply ax_int_l |].
  apply ax_cgr with (q := g (A + B));
    [constructor; constructor; assumption | apply cgr_choice_com].
Qed.

(** *** Stage 1's invariant, measure bookkeeping, and iteration

    [tau_cont_norm] is the *hypothesis* stage 1 consumes ("every
    [𝛕]-continuation is [⊢]-equal to some [tau_nf] guarded sum") and
    [tau_cont_nf] ([VCCS_Canonical.v] above) is what it *produces*
    (the continuation already **is** such a guarded sum, syntactically).
    The gap between the two is exactly one rewrite per summand, which is
    what [tau_normalize_conts] performs — repeatedly, with [ntodo] as its
    measure.

    Note [tau_cont_norm] is deliberately silent on non-[𝛕] summands
    ([True]), so it transports across [Permutation] and [rebuild] as
    cheaply as [tau_cont_nf] does. *)

Definition tau_cont_norm (a : gproc) : Prop :=
match a with
| 𝛕 • q => exists Y, gStatic Y /\ tau_nf Y /\ ax_pre q (g Y) /\ ax_pre (g Y) q
| _ => True
end.

Lemma tau_cont_norm_perm : forall l l', Permutation l l' ->
  Forall tau_cont_norm l -> Forall tau_cont_norm l'.
Proof.
  intros l l' Hp Hall.
  apply Forall_forall. intros x Hx.
  rewrite Forall_forall in Hall. apply Hall. rewrite Hp. exact Hx.
Qed.

Lemma tau_cont_norm_rebuild : forall l, Forall (fun a => summands a = [a]) l ->
  Forall tau_cont_norm l -> Forall tau_cont_norm (summands (rebuild l)).
Proof.
  induction l as [|a l IH]; intros Hlv Hall; simpl.
  - constructor; [exact I | constructor].
  - inversion Hlv as [|? ? Ha Hlv']; subst.
    inversion Hall as [|? ? Hok Hall']; subst.
    apply Forall_app. rewrite Ha. split.
    + constructor; [exact Hok | constructor].
    + apply IH; assumption.
Qed.

Lemma ntodo_summands_rebuild : forall l,
  Forall (fun a => summands a = [a]) l -> ntodo (summands (rebuild l)) = ntodo l.
Proof.
  induction l as [|a l IH]; intro Hall; simpl.
  - reflexivity.
  - inversion Hall as [|? ? Ha Hall']; subst.
    rewrite ntodo_app. rewrite Ha. simpl. rewrite (IH Hall'). lia.
Qed.

(** [simpl] eagerly unfolds [todo1] inside [ntodo], which destroys the
    shape the rewrites below need — this lemma exposes the [cons] step
    without touching the per-summand weight. *)

Lemma ntodo_cons : forall a l, ntodo (a :: l) = (todo1 a + ntodo l)%nat.
Proof. reflexivity. Qed.

(** Stage 1's iteration: turn [tau_cont_norm] into [tau_cont_nf], one
    [𝛕]-summand at a time. Each round selects an outstanding summand
    ([find_tau_todo]), rewrites its continuation in place
    ([ax_tau_cont_anywhere]) to the [tau_nf] guarded sum the invariant
    promises, and thereby drops [ntodo] by exactly one. *)

Theorem tau_normalize_conts : forall n M, gStatic M ->
  (ntodo (summands M) <= n)%nat ->
  Forall tau_cont_norm (summands M) ->
  exists M', gStatic M' /\ Forall tau_cont_nf (summands M')
             /\ ax_pre (g M) (g M') /\ ax_pre (g M') (g M).
Proof.
  induction n as [|n IH]; intros M HM Hmeas Hnorm.
  - exists M. repeat split; [exact HM | | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
    apply find_tau_todo_none.
    destruct (find_tau_todo (summands M)) as [(q,r)|] eqn:E; [| reflexivity].
    exfalso.
    destruct (find_tau_todo_spec _ _ _ E) as (Hperm & Htd).
    rewrite (ntodo_perm _ _ Hperm) in Hmeas.
    rewrite ntodo_cons in Hmeas.
    rewrite (todo1_pos _ Htd) in Hmeas.
    lia.
  - destruct (find_tau_todo (summands M)) as [(q,r)|] eqn:E.
    + destruct (find_tau_todo_spec _ _ _ E) as (Hperm & Htd).
      assert (Hnormperm : Forall tau_cont_norm ((𝛕 • q) :: r))
        by (eapply tau_cont_norm_perm; eassumption).
      inversion Hnormperm as [|? ? Hhd Hnormr]; subst.
      destruct Hhd as (Y & HYgst & HYnf & Hqf & Hqb).
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • q) :: r)).
      { apply Forall_forall. intros x Hx.
        pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite Hperm. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_cont_mid_static M q r HM Hperm) as (Hqst & Hrgst & _).
      destruct (ax_tau_cont_anywhere M q (g Y) r HM (static_g Y HYgst) Hperm Hqf Hqb)
        as (Hfwd & Hbwd).
      assert (Hnew : gStatic ((𝛕 • (g Y)) + rebuild r))
        by (constructor; [constructor; constructor; exact HYgst
                         | apply rebuild_gStatic; exact Hrgst]).
      assert (Htrue : tau_nfB Y = true) by (apply tau_nfB_spec; exact HYnf).
      assert (Hmeas2 : ntodo (summands ((𝛕 • (g Y)) + rebuild r)) <= n).
      { simpl summands. rewrite ntodo_cons.
        rewrite (ntodo_summands_rebuild r Hlvr).
        simpl todo1. rewrite Htrue.
        rewrite (ntodo_perm _ _ Hperm) in Hmeas.
        rewrite ntodo_cons in Hmeas.
        rewrite (todo1_pos _ Htd) in Hmeas.
        simpl. lia. }
      assert (Hnorm2 : Forall tau_cont_norm (summands ((𝛕 • (g Y)) + rebuild r))).
      { simpl summands. constructor.
        - exists Y. repeat split; [exact HYgst | exact HYnf | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
        - apply tau_cont_norm_rebuild; assumption. }
      destruct (IH _ Hnew Hmeas2 Hnorm2) as (M' & HM'st & HM'nf & Hf & Hb).
      exists M'. repeat split; [exact HM'st | exact HM'nf | |].
      * eapply ax_trans; [exact Hfwd | exact Hf].
      * eapply ax_trans; [exact Hb | exact Hbwd].
    + exists M. repeat split; [exact HM | | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
      apply find_tau_todo_none. exact E.
Qed.

Lemma tau_weight_summands_rebuild : forall l,
  Forall (fun a => summands a = [a]) l -> tau_weight (summands (rebuild l)) = tau_weight l.
Proof.
  induction l as [|a l IH]; intro Hall; simpl.
  - reflexivity.
  - inversion Hall as [|? ? Ha Hall']; subst.
    rewrite tau_weight_app. rewrite Ha. simpl.
    destruct a; rewrite (IH Hall'); lia.
Qed.

Lemma tau_cont_nf_of_tau_nf : forall Y, tau_nf Y -> Forall tau_cont_nf (summands Y).
Proof.
  intros Y H. destruct H.
  - apply Forall_forall. intros x Hx.
    pose proof (tau_cont_ok_stable M H) as Hok.
    rewrite Forall_forall in Hok. specialize (Hok x Hx).
    destruct x; simpl in *; try exact I.
    destruct Hok as (Z & HZ & HZst). exists Z. split; [exact HZ | apply tnf_stable; exact HZst].
  - simpl. constructor; [| constructor; [| constructor]].
    + exists M1. split; [reflexivity | exact H].
    + exists M2. split; [reflexivity | exact H0].
Qed.

Lemma tau_cont_nf_rebuild : forall l, Forall (fun a => summands a = [a]) l ->
  Forall tau_cont_nf l -> Forall tau_cont_nf (summands (rebuild l)).
Proof.
  induction l as [|a l IH]; intros Hlv Hall; simpl.
  - constructor; [exact I | constructor].
  - inversion Hlv as [|? ? Ha Hlv']; subst.
    inversion Hall as [|? ? Hok Hall']; subst.
    apply Forall_app. rewrite Ha. split.
    + constructor; [exact Hok | constructor].
    + apply IH; assumption.
Qed.

(** ** The flattening phase: [tau_cont_nf] becomes [tau_cont_ok]

    Repeatedly flatten a [𝛕]-summand whose continuation is a nested
    internal choice, until none is left. Measure: [tau_weight]. Note the
    base case relies on [gStableB Y = false] to rule out [①]/[𝟘], whose
    [gsize] is [0] and which would otherwise make the measure argument
    fail. *)

Theorem tau_flatten_all : forall n M, gStatic M ->
  (tau_weight (summands M) <= n)%nat ->
  Forall tau_cont_nf (summands M) ->
  exists M', gStatic M' /\ Forall tau_cont_ok (summands M')
             /\ ax_pre (g M) (g M') /\ ax_pre (g M') (g M).
Proof.
  induction n as [|n IH]; intros M HM Hmeas Hnf.
  - exists M. repeat split; [exact HM | | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
    apply find_unstable_tau_none; [| exact Hnf].
    destruct (find_unstable_tau (summands M)) as [(Y,r)|] eqn:E; [| reflexivity].
    exfalso. destruct (find_unstable_tau_spec _ _ _ E) as (Hperm & Hst).
    rewrite (tau_weight_perm _ _ Hperm) in Hmeas. simpl in Hmeas.
    destruct Y; simpl in *; try discriminate Hst; lia.
  - destruct (find_unstable_tau (summands M)) as [(Y,r)|] eqn:E.
    + destruct (find_unstable_tau_spec _ _ _ E) as (Hperm & Hstb).
      assert (Hnfperm : Forall tau_cont_nf ((𝛕 • (g Y)) :: r))
        by (eapply tau_cont_nf_perm; eassumption).
      inversion Hnfperm as [|? ? Hhd Hnfr]; subst.
      destruct Hhd as (Y0 & HY0 & HnfY). injection HY0 as HY0. subst Y0.
      assert (HAT : gAllTau Y).
      { destruct (tau_nf_gAllTau_or_stable Y HnfY) as [Hs|Ha]; [| exact Ha].
        exfalso. apply gStableB_spec in Hs. rewrite Hstb in Hs. discriminate Hs. }
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite Hperm. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM Hperm) as (HYgst & Hrgst & _).
      destruct (ax_tau_flatten_anywhere M Y r HM HAT Hperm) as (Hfwd & Hbwd).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : tau_weight (summands (rebuild r + Y)) <= n).
      { simpl. rewrite tau_weight_app. rewrite (tau_weight_summands_rebuild r Hlvr).
        rewrite (tau_weight_perm _ _ Hperm) in Hmeas. simpl in Hmeas.
        inversion HnfY as [? Hs | A B HA HB]; subst.
        - exfalso. apply gStableB_spec in Hs. rewrite Hstb in Hs. discriminate Hs.
        - simpl in *. lia. }
      assert (Hnf2 : Forall tau_cont_nf (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_nf_rebuild; assumption.
        - apply tau_cont_nf_of_tau_nf. exact HnfY. }
      destruct (IH (rebuild r + Y) Hnew Hmeas2 Hnf2) as (M' & HM'st & HM'ok & Hf & Hb).
      exists M'. repeat split; [exact HM'st | exact HM'ok | |].
      * eapply ax_trans; [exact Hfwd | exact Hf].
      * eapply ax_trans; [exact Hb | exact Hbwd].
    + exists M. repeat split; [exact HM | | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
      apply find_unstable_tau_none; [exact E | exact Hnf].
Qed.

Theorem tau_separate : forall n M, gStatic M ->
  (ntaus (summands M) <= n)%nat -> Forall tau_cont_ok (summands M) ->
  exists M', gStatic M' /\ tau_nf M' /\ ax_pre (g M) (g M') /\ ax_pre (g M') (g M).
Proof.
  induction n as [|n IH]; intros M HM Hmeas Hok.
  - exists M. repeat split; [exact HM | | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
    apply tnf_stable. apply find_tau_none_stable.
    destruct (find_tau (summands M)) as [(p,r)|] eqn:E; [| reflexivity].
    exfalso. apply find_tau_spec in E.
    rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia.
  - destruct (find_tau (summands M)) as [(p,r)|] eqn:E.
    + apply find_tau_spec in E.
      assert (Hokperm : Forall tau_cont_ok ((𝛕 • p) :: r))
        by (eapply tau_cont_ok_perm; eassumption).
      inversion Hokperm as [|? ? Hp0 Hokr]; subst.
      destruct Hp0 as (Y & Hpy & HYst). subst p.
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite E. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM E) as (HYgst & Hrgst & _).
      destruct (ax_tau_sep_anywhere M Y r HM E) as (Hfwd & Hbwd).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : ntaus (summands (rebuild r + Y)) <= n).
      { simpl. rewrite ntaus_app.
        rewrite (ntaus_summands_rebuild r Hlvr).
        rewrite (gStable_ntaus_zero Y HYst).
        rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia. }
      assert (Hok2 : Forall tau_cont_ok (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_ok_rebuild; assumption.
        - apply tau_cont_ok_stable. exact HYst. }
      destruct (IH (rebuild r + Y) Hnew Hmeas2 Hok2) as (M1 & HM1st & HM1nf & Hf1 & Hb1).
      exists ((𝛕 • (g M1)) + (𝛕 • (g Y))).
      repeat split.
      * constructor; constructor; constructor; assumption.
      * apply tnf_choice; [exact HM1nf | apply tnf_stable; exact HYst].
      * eapply ax_trans; [exact Hfwd | apply ax_choice_tau; exact Hf1].
      * eapply ax_trans; [apply ax_choice_tau; exact Hb1 | exact Hbwd].
    + exists M. repeat split; [exact HM | | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
      apply tnf_stable. apply find_tau_none_stable. exact E.
Qed.

(** ** The termination measure

    [nacts] counts the *action-bearing* summands, ignoring [①]/[𝟘]/[𝛕].
    Plain [length (summands _)] does **not** work as the measure: a
    collapse step rewrites [M] into [merged + rebuild r], and
    [summands (rebuild r)] is [r ++ [𝟘]] — [rebuild] emits a trailing
    [𝟘] — so the summand *count* is unchanged (two guards become one,
    but one [𝟘] appears). Counting only action-bearing summands fixes
    this exactly: the collapse replaces two of them by one, and the
    padding [𝟘] contributes nothing, so [nacts] strictly decreases. *)

Fixpoint nacts (l : list gproc) : nat :=
match l with
| [] => 0
| a :: l' => if decide (gact a = None) then nacts l' else S (nacts l')
end.

Lemma nacts_app : forall l1 l2, nacts (l1 ++ l2) = (nacts l1 + nacts l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl.
  - reflexivity.
  - destruct (decide (gact a = None)); [apply IH | rewrite IH; reflexivity].
Qed.

Lemma nacts_perm : forall l l', Permutation l l' -> nacts l = nacts l'.
Proof.
  intros l l' Hp. induction Hp; simpl.
  - reflexivity.
  - destruct (decide (gact x = None)); [exact IHHp | rewrite IHHp; reflexivity].
  - destruct (decide (gact y = None)); destruct (decide (gact x = None)); reflexivity.
  - rewrite IHHp1. exact IHHp2.
Qed.


Lemma nacts_summands_rebuild : forall l,
  Forall (fun a => summands a = [a]) l -> nacts (summands (rebuild l)) = nacts l.
Proof.
  induction l as [|a l IH]; intro Hall; simpl.
  - reflexivity.
  - inversion Hall as [|? ? Ha Hall']; subst.
    rewrite nacts_app. rewrite Ha. simpl.
    destruct (decide (gact a = None)); rewrite (IH Hall'); reflexivity.
Qed.

(** ** Recovering a guard's shape from its action *)

Lemma gact_input_shape : forall a c, gact a = Some (c, None) -> exists P, a = c ? P.
Proof.
  intros a c H. destruct a; simpl in H; try discriminate H.
  injection H as H1. subst. exists p. reflexivity.
Qed.

Lemma gact_output_shape : forall a c v, gact a = Some (c, Some v) -> exists P, a = c ! v • P.
Proof.
  intros a c v H. destruct a; simpl in H; try discriminate H.
  injection H as H1 H2. subst. exists p. reflexivity.
Qed.

(** ** Canonicalisation

    Every [gStatic] guarded sum is [⊢]-provably equal, in both
    directions, to a *canonical* one. By well-founded recursion on
    [nacts (summands M)]: [find_dup] either reports [None], in which case
    [M] is already canonical and [ax_refl] closes both directions, or
    produces a same-action pair, which [find_dup_spec] hands to
    [ax_collapse_input_anywhere]/[ax_collapse_output_anywhere] —
    dispatching on whether the pair's action has a value component, and
    recovering each guard's syntactic shape via
    [gact_input_shape]/[gact_output_shape]. The recursion then continues
    on [merged + rebuild r], and the two [ax_pre] chains compose by
    [ax_trans].

    The [𝛕]-summands are never touched: [gact] returns [None] for them,
    so [find_dup] never selects one, and they simply ride along inside
    [rebuild r]. That is exactly why [ax_choice_stable]'s freedom in its
    *context* argument matters — see the header comment. *)

Theorem canonicalize : forall M, gStatic M ->
  exists M', gStatic M' /\ canonical M' /\ ax_pre (g M) (g M') /\ ax_pre (g M') (g M).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ (fun M => nacts (summands M)) Nat.lt_wf_0)).
  intro HM.
  destruct (find_dup (summands M)) as [((a,b),r)|] eqn:E.
  - destruct (find_dup_spec (summands M) a b r E) as ((k & Hga & Hgb) & Hp).
    assert (Hleaves : Forall (fun x => summands x = [x]) (a :: b :: r)).
    { apply Forall_forall. intros x Hx.
      pose proof (summands_leaves M) as Hsl. rewrite Forall_forall in Hsl.
      apply Hsl. rewrite Hp. exact Hx. }
    inversion Hleaves as [|? ? _ Hlv2]; subst. inversion Hlv2 as [|? ? _ Hlv3]; subst.
    assert (Hallst : Forall gStatic (a :: b :: r)) by (eapply perm_summands_gStatic; eassumption).
    inversion Hallst as [|? ? HsP Hallst2]; subst.
    inversion Hallst2 as [|? ? HsQ Hallst3]; subst.
    destruct k as (c, [v|]).
    + destruct (gact_output_shape a c v Hga) as (P & Ha). subst a.
      destruct (gact_output_shape b c v Hgb) as (Q & Hb). subst b.
      inversion HsP; subst. inversion HsQ; subst.
      destruct (ax_collapse_output_anywhere M c v P Q r HM Hp) as (Hfwd & Hbwd).
      assert (HM0 : gStatic ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild r)).
      { constructor.
        - constructor. constructor. constructor; constructor; assumption.
        - apply rebuild_gStatic. assumption. }
      assert (Hmeas : nacts (summands ((c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild r)) < nacts (summands M)).
      { rewrite (nacts_perm _ _ Hp). simpl.
        rewrite (nacts_summands_rebuild r Hlv3). lia. }
      destruct (IH _ Hmeas HM0) as (M' & HM'st & HM'can & Hf & Hb).
      exists M'. repeat split; [exact HM'st | exact HM'can | | ].
      * eapply ax_trans; [exact Hfwd | exact Hf].
      * eapply ax_trans; [exact Hb | exact Hbwd].
    + destruct (gact_input_shape a c Hga) as (P & Ha). subst a.
      destruct (gact_input_shape b c Hgb) as (Q & Hb). subst b.
      inversion HsP; subst. inversion HsQ; subst.
      destruct (ax_collapse_input_anywhere M c P Q r HM Hp) as (Hfwd & Hbwd).
      assert (HM0 : gStatic ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild r)).
      { constructor.
        - constructor. constructor. constructor; constructor; assumption.
        - apply rebuild_gStatic. assumption. }
      assert (Hmeas : nacts (summands ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + rebuild r)) < nacts (summands M)).
      { rewrite (nacts_perm _ _ Hp). simpl.
        rewrite (nacts_summands_rebuild r Hlv3). lia. }
      destruct (IH _ Hmeas HM0) as (M' & HM'st & HM'can & Hf & Hb).
      exists M'. repeat split; [exact HM'st | exact HM'can | | ].
      * eapply ax_trans; [exact Hfwd | exact Hf].
      * eapply ax_trans; [exact Hb | exact Hbwd].
  - exists M. repeat split; [exact HM | exact E | apply ax_refl; constructor; assumption | apply ax_refl; constructor; assumption].
Qed.

End VCCS_Canonical.
