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

(** * The expansion law: [g M ‖ g N] as a guarded sum

    [ext]/[ext_r]/[int] compute the guarded-sum normal form of [M ‖ N]
    for two guarded sums [M], [N] — [ext M N] lets each of [M]'s own
    prefixes race ahead of the untouched [N]; [ext_r N M] is the mirror
    image for [N] racing ahead of [M] (a *separate* function, not just
    [ext] with swapped arguments — [ext]'s wrapping order is always
    "this argument's own continuation, then the other argument", so
    swapping arguments would wrap in the wrong order relative to
    [lts_parR]'s own target shape [g M ‖ c2], not [c2 ‖ g M]); [int M N]
    enumerates every input/output pair between [M] and [N] that can
    synchronise into a [𝛕]. Proved law:
    [g M ‖ g N ≂ₘᵤₛₜᵢ g ((ext M N + ext_r N M) + int M N)]
    ([must_i_expansion]/[must_i_expansion_l]/[must_i_expansion_r]
    below) — mirroring [lts_comL]/[lts_comR]'s own case split.

    Proved via a much more direct route than the acceptance-set
    machinery [VCCS_Precongruence.v] needed for [‖]-precongruence:
    [g M ‖ g N] and [g ((ext M N + ext_r N M) + int M N)] turn out to
    have *exactly* the same one-step [lts] transitions (same labels,
    same targets, not merely related ones) — [expansion_lts_iff] below
    — so a generic "same transitions ⟹ same [must]-behaviour" lemma
    ([must_same_lts]) closes the whole thing, no trace-interleaving or
    coR-abstraction reasoning needed at all. *)

From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization
  VCCS_Precongruence VCCS_ta_tc_gen.

Section VCCS_Expansion.

Context `{VP : VCCS_Parameters}.

(** ** A generic tool: identical one-step transitions give identical [must]-behaviour

    If [p] and [q] have exactly the same outgoing [τ] and external
    transitions (same labels, same targets), they must-pass exactly the
    same tests — proved by a direct induction on the [must] derivation,
    substituting [p]'s transitions for [q]'s (or vice versa) at each
    step; no relation on the *reached* states beyond "literally the
    same transition set" is needed, since [must]'s own recursive
    structure (the [pt]/[et]/[com] fields) only ever talks about
    one-step transitions. *)

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

(** ** [①] and [𝟘] are indistinguishable *as servers*

    [must p t]'s outcome field inspects only the *test*; the server
    enters solely through its transitions. [①] and [𝟘] have none at all
    — no [lts] constructor mentions either — so they must-pass exactly
    the same tests, and [must_same_lts] gives the equivalence in three
    lines.

    This is needed for completeness rather than for its own sake: a
    normal form may carry [①]/[𝟘] summands, and the derivation has to be
    able to discard them. Structural congruence removes a [𝟘] summand
    ([cgr_choice_nil]) but says nothing about [①], and no other rule
    mentions [①] at all — so [DefinitionAxiomatic.v] gains
    [ax_success_l]/[ax_success_r] for this, after which
    [ax_choice_stable] turns any [① ] summand into a [𝟘] and [ax_cgr]
    drops it. *)

Lemma must_i_success_nil : forall t, (g ①) must_pass t <-> (g 𝟘) must_pass t.
Proof.
  apply must_same_lts.
  - intro p'. split; intro H; inversion H.
  - intros mu p'. split; intro H; inversion H.
Qed.

Lemma must_i_success_nil_l : (g ①) ⊑ₘᵤₛₜᵢ (g 𝟘).
Proof. intros t Ht. apply must_i_success_nil. exact Ht. Qed.

Lemma must_i_success_nil_r : (g 𝟘) ⊑ₘᵤₛₜᵢ (g ①).
Proof. intros t Ht. apply must_i_success_nil. exact Ht. Qed.

(** ** [M]'s own prefixes race ahead of the untouched [N]

    The input case needs [gNewVar 0 N] (not [N] verbatim) to shift
    [N]'s own bound value variables out of the way of the new binder
    [c?_] introduces — the same "would-be-captured, so shift" reasoning
    as [NewVarC] under [ν] (see [Static_NewVarC]'s comment,
    [VCCS_Static.v]), but for value binders instead of channel binders. *)
Fixpoint ext (M N : gproc) : gproc :=
match M with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? p => c ? (p ‖ (g (gNewVar 0 N)))
| c ! v • p => c ! v • (p ‖ (g N))
| 𝛕 • p => 𝛕 • (p ‖ (g N))
| gp1 + gp2 => (ext gp1 N) + (ext gp2 N)
end.

(** [N]'s own prefixes race ahead of the untouched [M] — a *separate*
    function from [ext], not just [ext] with swapped arguments, so that
    the wrapping order matches [lts_parR]'s target shape [g M ‖ c2]
    (not [c2 ‖ g M]). *)
Fixpoint ext_r (N M : gproc) : gproc :=
match N with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? q => c ? ((g (gNewVar 0 M)) ‖ q)
| c ! v • q => c ! v • ((g M) ‖ q)
| 𝛕 • q => 𝛕 • ((g M) ‖ q)
| gq1 + gq2 => (ext_r gq1 M) + (ext_r gq2 M)
end.

(** Pair a specific input guard [c?p] (from one side) against every
    output guard of [N] (the other side) on the same channel. *)
Fixpoint int_input (c : ChannelData) (p : proc) (N : gproc) {struct N} : gproc :=
match N with
| ① => 𝟘
| 𝟘 => 𝟘
| c' ? q => 𝟘
| c' ! v' • q => if decide (c = c') then 𝛕 • (p^v' ‖ q) else 𝟘
| 𝛕 • q => 𝟘
| gq1 + gq2 => (int_input c p gq1) + (int_input c p gq2)
end.

(** Symmetric: pair a specific output guard [c!v•p] against every input
    guard of [N] on the same channel. *)
Fixpoint int_output (c : ChannelData) (v : ValueData) (p : proc) (N : gproc) {struct N} : gproc :=
match N with
| ① => 𝟘
| 𝟘 => 𝟘
| c' ? q => if decide (c = c') then 𝛕 • (p ‖ (q^v)) else 𝟘
| c' ! v' • q => 𝟘
| 𝛕 • q => 𝟘
| gq1 + gq2 => (int_output c v p gq1) + (int_output c v p gq2)
end.

(** All synchronisations between [M] and [N] — dispatches on [M]'s own
    guard kind and searches [N] for the complement, so a single call
    [int M N] already covers both sync directions (input-then-output
    and output-then-input); no separate [int N M] is needed. *)
Fixpoint int (M N : gproc) : gproc :=
match M with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? p => int_input c p N
| c ! v • p => int_output c v p N
| 𝛕 • p => 𝟘
| gp1 + gp2 => (int gp1 N) + (int gp2 N)
end.

(** ** [Static] reflects the value-substitution shift: [gproc] cancellation

    [subst_in_proc 0 v (NewVar 0 p) = p] is already proved (as
    [All_According], [VCCS_ta_tc_gen.v]) for arbitrary [proc]; injecting
    through the [g] coercion (a genuine constructor, hence injective)
    gives the [gproc]-level fact needed for [ext]/[ext_r]'s input case. *)

Lemma gproc_NewVar_cancel : forall N v, subst_in_gproc 0 v (gNewVar 0 N) = N.
Proof.
  intros N v.
  pose proof (All_According (g N) 0 v) as H.
  simpl in H. injection H as H. exact H.
Qed.

(** ** [ext]/[ext_r] exactly mirror [M]/[N]'s own transitions

    [ext M N]'s transitions are in bijection with [M]'s own transitions,
    each wrapped with [‖ g N] — same label, same (wrapped) target, not
    merely a related one. *)

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
    + inversion H; subst. apply lts_output.
    + inversion H; subst. apply lts_output.
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
      replace (g M ‖ p^v) with ((g (gNewVar 0 M) ‖ p) ^ v).
      * apply lts_input.
      * simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + inversion H; subst. apply lts_input.
  - split; intro H.
    + inversion H; subst. apply lts_output.
    + inversion H; subst. apply lts_output.
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

(** The "shape" corollaries: every transition [ext M N] (resp. [ext_r N
    M]) can take lands on a target of the wrapped shape — needed to
    invert an *arbitrary* target back to the underlying [M]/[N]
    transition (the "forall tgt" phrasing of [ext_lts_iff] alone isn't
    enough for that direction, since it doesn't itself say every target
    of [ext M N] has this shape). *)

Lemma ext_lts_shape : forall M N a tgt, lts (g (ext M N)) a tgt -> exists tgt', tgt = tgt' ‖ g N /\ lts (g M) a tgt'.
Proof.
  induction M; intros N a tgt H; simpl in H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    exists (p^v). split.
    + simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + apply lts_input.
  - inversion H; subst. exists p. split; [reflexivity | apply lts_output].
  - inversion H; subst. exists p. split; [reflexivity | apply lts_tau].
  - inversion H; subst.
    + apply IHM1 in H4 as (tgt' & Heq & H4'). exists tgt'. split; [exact Heq | apply lts_choiceL; exact H4'].
    + apply IHM2 in H4 as (tgt' & Heq & H4'). exists tgt'. split; [exact Heq | apply lts_choiceR; exact H4'].
Qed.

Lemma ext_r_lts_shape : forall N M a tgt, lts (g (ext_r N M)) a tgt -> exists tgt', tgt = g M ‖ tgt' /\ lts (g N) a tgt'.
Proof.
  induction N; intros M a tgt H; simpl in H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    exists (p^v). split.
    + simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + apply lts_input.
  - inversion H; subst. exists p. split; [reflexivity | apply lts_output].
  - inversion H; subst. exists p. split; [reflexivity | apply lts_tau].
  - inversion H; subst.
    + apply IHN1 in H4 as (tgt' & Heq & H4'). exists tgt'. split; [exact Heq | apply lts_choiceL; exact H4'].
    + apply IHN2 in H4 as (tgt' & Heq & H4'). exists tgt'. split; [exact Heq | apply lts_choiceR; exact H4'].
Qed.

(** ** [int]'s transitions are exactly [M]/[N]'s synchronisations *)

Lemma int_input_lts_iff : forall c p N tgt,
  lts (g (int_input c p N)) τ tgt <->
    exists v q, lts (g N) ((c,v)!) q /\ tgt = p^v ‖ q.
Proof.
  induction N; intros tgt; simpl.
  - split; [intro H; inversion H | intros (v & q & H & _); inversion H].
  - split; [intro H; inversion H | intros (v & q & H & _); inversion H].
  - split.
    + intro H; inversion H.
    + intros (v & q & H & Heq). inversion H.
  - destruct (decide (c = c0)) as [Heq0|Hneq0]; subst.
    + split.
      * intro H. inversion H; subst. exists v, p0. split; [apply lts_output | reflexivity].
      * intros (v0 & q & H & Heq). inversion H; subst. apply lts_tau.
    + split.
      * intro H; inversion H.
      * intros (v0 & q & H & Heq). inversion H; subst. exfalso. apply Hneq0. reflexivity.
  - split.
    + intro H; inversion H.
    + intros (v & q & H & Heq). inversion H.
  - split.
    + intro H.
      inversion H; subst.
      * apply IHN1 in H4 as (v & q & H4' & Heq). exists v, q. split; [apply lts_choiceL; exact H4' | exact Heq].
      * apply IHN2 in H4 as (v & q & H4' & Heq). exists v, q. split; [apply lts_choiceR; exact H4' | exact Heq].
    + intros (v & q & H & Heq). inversion H; subst.
      * apply lts_choiceL. apply IHN1. exists v, q. split; [exact H4 | reflexivity].
      * apply lts_choiceR. apply IHN2. exists v, q. split; [exact H4 | reflexivity].
Qed.

Lemma int_output_lts_iff : forall c v p N tgt,
  lts (g (int_output c v p N)) τ tgt <->
    exists q', lts (g N) ((c,v)?) q' /\ tgt = p ‖ q'.
Proof.
  induction N; intros tgt; simpl.
  - split; [intro H; inversion H | intros (q & H & _); inversion H].
  - split; [intro H; inversion H | intros (q & H & _); inversion H].
  - destruct (decide (c = c0)) as [Heq0|Hneq0]; subst.
    + split.
      * intro H. inversion H; subst. exists (p0^v). split; [apply lts_input | reflexivity].
      * intros (q & H & Heq). inversion H; subst. apply lts_tau.
    + split.
      * intro H; inversion H.
      * intros (q & H & Heq). inversion H; subst. exfalso. apply Hneq0. reflexivity.
  - split.
    + intro H; inversion H.
    + intros (q & H & Heq). inversion H.
  - split.
    + intro H; inversion H.
    + intros (q & H & Heq). inversion H.
  - split.
    + intro H.
      inversion H; subst.
      * apply IHN1 in H4 as (q & H4' & Heq). exists q. split; [apply lts_choiceL; exact H4' | exact Heq].
      * apply IHN2 in H4 as (q & H4' & Heq). exists q. split; [apply lts_choiceR; exact H4' | exact Heq].
    + intros (q & H & Heq). inversion H; subst.
      * apply lts_choiceL. apply IHN1. exists q. split; [exact H4 | reflexivity].
      * apply lts_choiceR. apply IHN2. exists q. split; [exact H4 | reflexivity].
Qed.

Lemma int_lts_iff : forall M N tgt,
  lts (g (int M N)) τ tgt <->
    (exists c v p q, lts (g M) ((c,v)!) p /\ lts (g N) ((c,v)?) q /\ tgt = p ‖ q) \/
    (exists c v p q, lts (g M) ((c,v)?) p /\ lts (g N) ((c,v)!) q /\ tgt = p ‖ q).
Proof.
  induction M; intros N tgt; simpl.
  - split.
    + intro H; inversion H.
    + intros [(c&v&p&q&H&_&_)|(c&v&p&q&H&_&_)]; inversion H.
  - split.
    + intro H; inversion H.
    + intros [(c&v&p&q&H&_&_)|(c&v&p&q&H&_&_)]; inversion H.
  - split.
    + intro H.
      apply int_input_lts_iff in H as (v & q & Hq & Heq).
      right. exists c, v, (p^v), q. split; [apply lts_input | split; [exact Hq | exact Heq]].
    + intros [(c'&v&p'&q&H&_&_)|(c'&v&p'&q&H&Hq&Heq)].
      * inversion H.
      * inversion H; subst. apply int_input_lts_iff. exists v, q. split; [exact Hq | reflexivity].
  - split.
    + intro H.
      apply int_output_lts_iff in H as (q & Hq & Heq).
      left. exists c, v, p, q. split; [apply lts_output | split; [exact Hq | exact Heq]].
    + intros [(c'&v'&p'&q&H&Hq&Heq)|(c'&v'&p'&q&H&_&_)].
      * inversion H; subst. apply int_output_lts_iff. exists q. split; [exact Hq | reflexivity].
      * inversion H.
  - split.
    + intro H; inversion H.
    + intros [(c&v&p'&q&H&_&_)|(c&v&p'&q&H&_&_)]; inversion H.
  - split.
    + intro H.
      inversion H; subst.
      * apply IHM1 in H4 as [(c&v&p'&q&H1&H2&H3)|(c&v&p'&q&H1&H2&H3)].
        -- left. exists c,v,p',q. split; [apply lts_choiceL; exact H1 | split; [exact H2|exact H3]].
        -- right. exists c,v,p',q. split; [apply lts_choiceL; exact H1 | split; [exact H2|exact H3]].
      * apply IHM2 in H4 as [(c&v&p'&q&H1&H2&H3)|(c&v&p'&q&H1&H2&H3)].
        -- left. exists c,v,p',q. split; [apply lts_choiceR; exact H1 | split; [exact H2|exact H3]].
        -- right. exists c,v,p',q. split; [apply lts_choiceR; exact H1 | split; [exact H2|exact H3]].
    + intros [(c&v&p'&q&H1&H2&H3)|(c&v&p'&q&H1&H2&H3)]; inversion H1; subst.
      * apply lts_choiceL. apply IHM1. left. exists c,v,p',q. auto.
      * apply lts_choiceR. apply IHM2. left. exists c,v,p',q. auto.
      * apply lts_choiceL. apply IHM1. right. exists c,v,p',q. auto.
      * apply lts_choiceR. apply IHM2. right. exists c,v,p',q. auto.
Qed.

(** [int]'s own transitions are always [τ] (it's built entirely from
    [𝛕•_]-guarded summands) — needed to discharge [int]'s contribution
    when comparing *external*-labelled transitions. *)

Lemma int_input_no_ext : forall c p N mu tgt, ~ lts (g (int_input c p N)) (ActExt mu) tgt.
Proof.
  induction N; intros mu tgt Hc; simpl in Hc.
  - inversion Hc.
  - inversion Hc.
  - inversion Hc.
  - destruct (decide (c=c0)); subst; inversion Hc.
  - inversion Hc.
  - inversion Hc; subst.
    + eapply IHN1; exact H3.
    + eapply IHN2; exact H3.
Qed.

Lemma int_output_no_ext : forall c v p N mu tgt, ~ lts (g (int_output c v p N)) (ActExt mu) tgt.
Proof.
  induction N; intros mu tgt Hc; simpl in Hc.
  - inversion Hc.
  - inversion Hc.
  - destruct (decide (c=c0)); subst; inversion Hc.
  - inversion Hc.
  - inversion Hc.
  - inversion Hc; subst.
    + eapply IHN1; exact H3.
    + eapply IHN2; exact H3.
Qed.

Lemma int_no_ext : forall M N mu tgt, ~ lts (g (int M N)) (ActExt mu) tgt.
Proof.
  induction M; intros N mu tgt Hc; simpl in Hc.
  - inversion Hc.
  - inversion Hc.
  - eapply int_input_no_ext; exact Hc.
  - eapply int_output_no_ext; exact Hc.
  - inversion Hc.
  - inversion Hc; subst.
    + eapply IHM1; exact H3.
    + eapply IHM2; exact H3.
Qed.

(** ** [g M ‖ g N] and the flattened guarded sum have exactly the same transitions *)

Lemma expansion_lts_iff : forall M N a tgt,
  lts (g M ‖ g N) a tgt <->
    lts (g (ext M N)) a tgt \/ lts (g (ext_r N M)) a tgt \/ (a = τ /\ lts (g (int M N)) τ tgt).
Proof.
  intros M N a tgt. split.
  - intro H. inversion H; subst.
    + right. right. split; [reflexivity|].
      apply int_lts_iff. left. exists c, v, p2, q2. auto.
    + right. right. split; [reflexivity|].
      apply int_lts_iff. right. exists c, v, q2, p2. auto.
    + left. apply ext_lts_iff. exact H4.
    + right. left. apply ext_r_lts_iff. exact H4.
  - intros [H|[H|(Ha&H)]].
    + apply ext_lts_shape in H as (tgt' & Heq & H'). subst. apply lts_parL. exact H'.
    + apply ext_r_lts_shape in H as (tgt' & Heq & H'). subst. apply lts_parR. exact H'.
    + subst. apply int_lts_iff in H as [(c&v&p&q&H1&H2&H3)|(c&v&p&q&H1&H2&H3)]; subst.
      * eapply lts_comL; [exact H1 | exact H2].
      * eapply lts_comR; [exact H2 | exact H1].
Qed.

Lemma lts_choice3_iff : forall A B C a tgt, lts (g ((A+B)+C)) a tgt <-> lts (g A) a tgt \/ lts (g B) a tgt \/ lts (g C) a tgt.
Proof.
  intros A B C a tgt. split.
  - intro H. inversion H; subst.
    + inversion H4; subst; [left; exact H5 | right; left; exact H5].
    + right. right. exact H4.
  - intros [H|[H|H]].
    + apply lts_choiceL. apply lts_choiceL. exact H.
    + apply lts_choiceL. apply lts_choiceR. exact H.
    + apply lts_choiceR. exact H.
Qed.

(** ** The expansion law *)

Theorem must_i_expansion : forall M N t,
  (g M ‖ g N) must_pass t <-> g ((ext M N + ext_r N M) + int M N) must_pass t.
Proof.
  intros M N t.
  apply must_same_lts.
  - intro p'. split.
    + intro H. apply lts_choice3_iff. apply expansion_lts_iff in H as [H|[H|(Ha&H)]]; auto.
    + intro H. apply expansion_lts_iff. apply lts_choice3_iff in H as [H|[H|H]]; auto.
  - intros mu p'. split.
    + intro H. apply lts_choice3_iff. apply expansion_lts_iff in H as [H|[H|(Ha&H)]]; auto. discriminate Ha.
    + intro H. apply expansion_lts_iff. apply lts_choice3_iff in H as [H|[H|H]]; auto.
      exfalso. eapply int_no_ext. exact H.
Qed.

Corollary must_i_expansion_l : forall M N, (g M ‖ g N) ⊑ₘᵤₛₜᵢ g ((ext M N + ext_r N M) + int M N).
Proof. intros M N t H. apply must_i_expansion. exact H. Qed.

Corollary must_i_expansion_r : forall M N, g ((ext M N + ext_r N M) + int M N) ⊑ₘᵤₛₜᵢ (g M ‖ g N).
Proof. intros M N t H. apply must_i_expansion. exact H. Qed.

(** ** [ext]/[ext_r]/[int] preserve [gStatic]

    Needed for [SoundnessAx.v]'s [ax_pre_static_preserved] once the
    expansion law becomes an [ax_pre] axiom ([DefinitionAxiomatic.v]'s
    [ax_expansion_l]/[ax_expansion_r]): [Static] must be shown to be an
    invariant of *every* [ax_pre] constructor, including these two. *)

Lemma ext_gStatic : forall M N, gStatic M -> gStatic N -> gStatic (ext M N).
Proof.
  induction M; intros N HM HN; simpl; inversion HM; subst.
  - constructor.
  - constructor.
  - constructor. constructor; [assumption | constructor; apply gStatic_gNewVar; assumption].
  - constructor. constructor; [assumption | constructor; assumption].
  - constructor. constructor; [assumption | constructor; assumption].
  - constructor; [apply IHM1 | apply IHM2]; assumption.
Qed.

Lemma ext_r_gStatic : forall N M, gStatic N -> gStatic M -> gStatic (ext_r N M).
Proof.
  induction N; intros M HN HM; simpl; inversion HN; subst.
  - constructor.
  - constructor.
  - constructor. constructor; [constructor; apply gStatic_gNewVar; assumption | assumption].
  - constructor. constructor; [constructor; assumption | assumption].
  - constructor. constructor; [constructor; assumption | assumption].
  - constructor; [apply IHN1 | apply IHN2]; assumption.
Qed.

Lemma int_input_gStatic : forall c p N, Static p -> gStatic N -> gStatic (int_input c p N).
Proof.
  intros c p N Hp HN. induction HN; simpl.
  - constructor.
  - constructor.
  - constructor.
  - destruct (decide (c = c0)); [repeat constructor; [apply Static_subst|]|constructor]; assumption.
  - constructor.
  - constructor; assumption.
Qed.

Lemma int_output_gStatic : forall c v p N, Static p -> gStatic N -> gStatic (int_output c v p N).
Proof.
  intros c v p N Hp HN. induction HN; simpl.
  - constructor.
  - constructor.
  - destruct (decide (c = c0)); [repeat constructor; [|apply Static_subst]|constructor]; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma int_gStatic : forall M N, gStatic M -> gStatic N -> gStatic (int M N).
Proof.
  induction M; intros N HM HN; simpl; inversion HM; subst.
  - constructor.
  - constructor.
  - apply int_input_gStatic; assumption.
  - apply int_output_gStatic; assumption.
  - constructor.
  - constructor; [apply IHM1 | apply IHM2]; assumption.
Qed.

End VCCS_Expansion.
