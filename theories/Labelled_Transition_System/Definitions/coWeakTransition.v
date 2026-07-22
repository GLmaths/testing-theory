(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From TestingTheory Require Import ActTau ForAllHelper MultisetHelper gLts Bisimulation
  Lts_OBA Lts_FW WeakTransitions.

(** ** Co-weak transitions

    [cowt p s q] is the weak transition relation obtained by letting [p] answer
    with a dual (co-)action of every external action recorded in the trace
    [s]: a step labelled [μ] in [s] is realised in the underlying LTS by any
    action [μ'] such that [dual μ' μ]. Everything below is phrased with the
    relation [dual]/[Forall2 dual] directly, so that a [cowt] fact can always
    be read back as a plain [wt] fact against *some* trace pointwise dual to
    [s] ([cowt_to_wt_dual]), and conversely built from one ([wt_to_cowt_dual]). *)

(** *** Definition of co-weak transitions *)

Inductive cowt `{gLts P A} : P -> trace A -> P -> Prop :=
| cowt_nil p : cowt p [] p
| cowt_tau s p q t (l : p ⟶ q) (w : cowt q s t) : cowt p s t
| cowt_act μ μ' s p q t (duo : dual μ' μ) (l : p ⟶[μ'] q) (w : cowt q s t) : cowt p (μ :: s) t
.

Global Hint Constructors cowt:mdb.

Notation "p ⟹ᶜᵒ q" := (cowt p [] q) (at level 30).
Notation "p ⟹ᶜᵒ{ μ } q" := (cowt p [μ] q) (at level 30, format "p  ⟹ᶜᵒ{ μ }  q").
Notation "p ⟹ᶜᵒ[ s ] q" := (cowt p s q) (at level 30, format "p  ⟹ᶜᵒ[ s ]  q").

Definition cowt_sc `{gLtsEq P H} p s q := ∃ r, p ⟹ᶜᵒ[s] r /\ r ⋍ q.

Notation "p ⟹ᶜᵒ⋍ q" := (cowt_sc p [] q) (at level 30, format "p  ⟹ᶜᵒ⋍  q").
Notation "p ⟹ᶜᵒ⋍{ μ } q" := (cowt_sc p [μ] q) (at level 30, format "p  ⟹ᶜᵒ⋍{ μ }  q").
Notation "p ⟹ᶜᵒ⋍[ s ] q" := (cowt_sc p s q) (at level 30, format "p  ⟹ᶜᵒ⋍[ s ]  q").

(** *** Properties on co-weak transitions in LTSs *)

(* As for [wt_pop_gen], the trace is kept as a variable and constrained by an
   equation so that plain induction applies. *)
Lemma cowt_pop_gen `{gLts P A} p q s0 :
  p ⟹ᶜᵒ[s0] q -> forall μ s, s0 = μ :: s -> ∃ t, p ⟹ᶜᵒ{μ} t /\ t ⟹ᶜᵒ[s] q.
Proof.
  intro w.
  induction w as [ p | s0 p r q l w IH | ν ν' s0 p r q duo l w IH ]; intros μ s Heq.
  - discriminate.
  - destruct (IH μ s Heq) as (t & w1 & w2).
    exists t. split; eauto with mdb.
  - inversion Heq; subst.
    exists r. split; eauto with mdb.
Qed.

Lemma cowt_pop `{gLts P A} p q μ s : p ⟹ᶜᵒ[μ :: s] q -> ∃ t, p ⟹ᶜᵒ{μ} t /\ t ⟹ᶜᵒ[s] q.
Proof. intro w. eapply cowt_pop_gen; eauto. Qed.

Lemma cowt_concat `{gLts P A} p q r s1 s2 :
  p ⟹ᶜᵒ[s1] q -> q ⟹ᶜᵒ[s2] r -> p ⟹ᶜᵒ[s1 ++ s2] r.
Proof. intros w1 w2. dependent induction w1; simpl; eauto with mdb. Qed.

Lemma cowt_push_left `{gLts P A} {p q r μ s} :
  p ⟹ᶜᵒ{μ} q -> q ⟹ᶜᵒ[s] r -> p ⟹ᶜᵒ[μ :: s] r.
Proof.
  intros w1 w2.
  replace (μ :: s) with ([μ] ++ s) by eauto.
  eapply cowt_concat; eauto.
Qed.

Lemma cowt_split `{gLts P A} p q s1 s2 :
  p ⟹ᶜᵒ[s1 ++ s2] q -> ∃ r, p ⟹ᶜᵒ[s1] r /\ r ⟹ᶜᵒ[s2] q.
Proof.
  revert p q.
  dependent induction s1; intros p q w.
  - eauto with mdb.
  - simpl in w. eapply cowt_pop in w as (r & w1 & w2).
    eapply IHs1 in w2 as (r' & w2 & w3).
    exists r'. split. eapply cowt_push_left; eauto. assumption.
Qed.

Lemma cowt_push_nil_left `{gLts P A} {p q r s} : p ⟹ᶜᵒ q -> q ⟹ᶜᵒ[s] r -> p ⟹ᶜᵒ[s] r.
Proof.
  intros w1 w2.
  remember ([] : trace A) as s0 eqn:Hs.
  revert Hs w2.
  induction w1 as [ x | s1 x y z lt w1 IH | μ μ' s1 x y z duo lt w1 IH ]; intros Hs w2.
  - exact w2.
  - eapply cowt_tau; [exact lt | eapply IH; [exact Hs | exact w2]].
  - discriminate.
Qed.

Lemma cowt_push_nil_right `{gLts P A} p q r s : p ⟹ᶜᵒ[s] q -> q ⟹ᶜᵒ r -> p ⟹ᶜᵒ[s] r.
Proof.
  intros w1 w2. replace s with (s ++ ([] : trace A)).
  eapply cowt_concat; eauto. eapply app_nil_r.
Qed.

Lemma cowt_push_right `{gLts P A} p q r μ s :
  p ⟹ᶜᵒ[s] q -> q ⟹ᶜᵒ{μ} r -> p ⟹ᶜᵒ[s ++ [μ]] r.
Proof. intros w1 w2. eapply cowt_concat; eauto. Qed.

(* Same treatment as [cowt_pop]: the trace stays a variable, so no UIP axiom. *)
Lemma cowt_decomp_one_gen `{gLts P A} p q s0 :
  p ⟹ᶜᵒ[s0] q -> forall μ, s0 = [μ] -> ∃ r1 r2 μ', p ⟹ᶜᵒ r1 ∧ dual μ' μ ∧ r1 ⟶[μ'] r2 ∧ r2 ⟹ᶜᵒ q.
Proof.
  intro w.
  induction w as [ p | s0 p r q l w IH | ν ν' s0 p r q duo l w IH ]; intros μ Heq.
  - discriminate.
  - destruct (IH μ Heq) as (r1 & r2 & μ' & w1 & duo' & l' & w2).
    exists r1, r2, μ'. repeat split; eauto with mdb.
  - inversion Heq; subst.
    exists p, r, ν'. repeat split; eauto with mdb.
Qed.

Lemma cowt_decomp_one `{gLts P A} {μ p q} :
  p ⟹ᶜᵒ{μ} q -> ∃ r1 r2 μ', p ⟹ᶜᵒ r1 ∧ dual μ' μ ∧ r1 ⟶[μ'] r2 ∧ r2 ⟹ᶜᵒ q.
Proof. intro w. eapply cowt_decomp_one_gen; eauto. Qed.

Lemma cowt_join_nil `{gLts P A} {p q r} : p ⟹ᶜᵒ q -> q ⟹ᶜᵒ r -> p ⟹ᶜᵒ r.
Proof. intros w1 w2. eapply cowt_push_nil_left; [exact w1 | exact w2]. Qed.

Lemma lts_to_cowt `{gLts P A} {p q μ μ'} : dual μ' μ -> p ⟶[μ'] q -> p ⟹ᶜᵒ{μ} q.
Proof. eauto with mdb. Qed.

Lemma lts_to_cowt_tau `{gLts P A} {p q} : p ⟶ q -> p ⟹ᶜᵒ q.
Proof. intros tr'. eapply cowt_tau;eauto. constructor. Qed.

(** *** Properties on co-weak transitions in LTSs with a Bisimulation *)

Lemma eq_spec_cowt `{gLtsEq P A} p p' : p ⋍ p' -> forall q s, p ⟹ᶜᵒ[s] q -> p' ⟹ᶜᵒ⋍[s] q.
Proof.
  intros heq q s w.
  revert p' heq.
  dependent induction w; intros.
  + exists p'; split. eauto with mdb. now symmetry.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
Qed.

Lemma lts_sc_to_cowt_sc `{gLtsEq P A} {p q μ μ'} : dual μ' μ -> p ⟶⋍[μ'] q -> p ⟹ᶜᵒ⋍{ μ } q.
Proof. intros duo (p' & tr' & eq). exists p'. split. eapply lts_to_cowt; eauto. eauto with mdb. Qed.

Lemma lts_sc_to_cowt_tau_sc `{gLtsEq P A} {p q} : p ⟶⋍ q -> p ⟹ᶜᵒ⋍ q.
Proof. intros (p' & tr' & eq). exists p'. split. eapply cowt_tau;eauto. eapply cowt_nil. eauto with mdb. Qed.

Lemma cowt_join_nil_eq `{gLtsEq P A} {p q r} : p ⟹ᶜᵒ⋍ q -> q ⟹ᶜᵒ⋍ r -> p ⟹ᶜᵒ⋍ r.
Proof.
  intros (q' & hwq' & heqq') (r' & hwr' & heqr').
  destruct (eq_spec_cowt _ _ (symmetry heqq') r' [] hwr') as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (cowt_push_nil_left hwq' hwr1). etrans; eassumption.
Qed.

Lemma cowt_join_nil_eq_l `{gLtsEq P A} {p q r s} : p ⟹ᶜᵒ⋍ q -> q ⟹ᶜᵒ[s] r -> p ⟹ᶜᵒ⋍[s] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_cowt _ _ (symmetry heqq') r s w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (cowt_push_nil_left hwq' hwr1). eassumption.
Qed.

Lemma cowt_join_nil_eq_r `{gLtsEq P A} {p q r s} : p ⟹ᶜᵒ[s] q -> q ⟹ᶜᵒ⋍ r -> p ⟹ᶜᵒ⋍[s] r.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply cowt_push_nil_right; eauto. eassumption.
Qed.

Lemma cowt_join_eq `{gLtsEq P A} {p q r s1 s2} : p ⟹ᶜᵒ⋍[s1] q -> q ⟹ᶜᵒ⋍[s2] r -> p ⟹ᶜᵒ⋍[s1 ++ s2] r.
  revert p q r s2.
Proof.
  induction s1; intros p q r s2 (q' & hwq' & heqq') w2; simpl in *.
  - destruct w2 as  (r' & hwr' & heqr').
    destruct (eq_spec_cowt _ _ (symmetry heqq') r' s2 hwr') as (r1 & hwr1 & heqr1).
    exists r1. split. eapply (cowt_push_nil_left hwq' hwr1). etrans; eassumption.
  - eapply cowt_pop in hwq' as (p0 & w0 & w1).
    edestruct IHs1 as (t' & hwt' & heqt').
    exists q'. split; eassumption. eassumption.
    exists t'. split. eapply (cowt_push_left w0 hwt'). eassumption.
Qed.

Lemma cowt_join_eq_l `{gLtsEq P A} {p q r s1 s2} : p ⟹ᶜᵒ⋍[s1] q -> q ⟹ᶜᵒ[s2] r -> p ⟹ᶜᵒ⋍[s1 ++ s2] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_cowt _ _ (symmetry heqq') r s2 w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply cowt_concat; eassumption. eassumption.
Qed.

Lemma cowt_join_eq_r `{gLtsEq P A} {p q r s1 s2} :
  p ⟹ᶜᵒ[s1] q -> q ⟹ᶜᵒ⋍[s2] r
    -> p ⟹ᶜᵒ⋍[s1 ++ s2] r.
Proof.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply cowt_concat; eassumption. eassumption.
Qed.

(** *** From [cowt] to [wt] and back, along an explicit dual trace

    [cowt p s q] unwinds to a genuine weak transition [wt p s' q] for the
    trace [s'] of the actual (dual) actions taken; conversely, any [wt p s' q]
    together with a trace [s] pointwise dual to [s'] gives a [cowt p s q].
    Both directions only ever use [dual]/[Forall2 dual], never the canonical
    co-action or its uniqueness. *)

Lemma cowt_to_wt_dual `{gLts P A} p s q : p ⟹ᶜᵒ[s] q -> exists s', Forall2 dual s s' /\ p ⟹[s'] q.
Proof.
  induction 1 as [ p | s p q t l w IH | μ μ' s p q t duo l w IH ].
  - exists []. split; constructor.
  - destruct IH as (s' & hf & w'). exists s'. split; [exact hf | eauto with mdb].
  - destruct IH as (s' & hf & w'). exists (μ' :: s'). split.
    + constructor; [symmetry; exact duo | exact hf].
    + eauto with mdb.
Qed.

Lemma wt_to_cowt_dual `{gLts P A} p s' q : p ⟹[s'] q -> forall s, Forall2 dual s s' -> p ⟹ᶜᵒ[s] q.
Proof.
  induction 1 as [ p | s' p q t l w IH | μ' s' p q t l w IH ]; intros s hf.
  - inversion hf; subst. constructor.
  - eapply cowt_tau; eauto.
  - inversion hf as [| x y la lb dxy hrest]; subst.
    eapply cowt_act; [symmetry; exact dxy | exact l | eapply IH; exact hrest].
Qed.

(** *** Properties on co-weak transitions in Lts with OBA axioms

    [co_non_blocking μ] says that *every* action dual to [μ] is non-blocking;
    unlike [exist_co_nba] (which only asks for existence and is what
    [forward_s]/[EquivDef] already use to *build* a dual trace) the universal
    form is what let us reason about the specific dual action a [cowt]
    derivation happens to use, without any determinacy assumption on [dual]. *)

Definition co_non_blocking `{ExtAction A} (μ : A) := forall μ', dual μ' μ -> non_blocking μ'.

Lemma refuses_tau_preserved_by_cowt_non_blocking_action `{gLtsOba P A} p q s :
  Forall co_non_blocking s -> p ↛ -> p ⟹ᶜᵒ[s] q -> q ↛.
Proof.
  intros s_spec hst hw.
  induction hw; eauto.
  - exfalso. eapply lts_refuses_spec2; eauto.
  - inversion s_spec; subst.
    eapply IHhw. eassumption. eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
Qed.

Lemma refuses_tau_action_preserved_by_cowt_non_blocking_action `{gLtsOba P A} p q s μ :
  Forall co_non_blocking s -> p ↛ -> p ↛[μ] -> p ⟹ᶜᵒ[s] q -> q ↛[μ].
Proof.
  intros s_spec hst_tau hst_inp hw.
  induction hw; eauto.
  - exfalso. eapply lts_refuses_spec2; eauto.
  - inversion s_spec; subst.
    eapply IHhw; eauto.
    + eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    + eapply refuses_action_preserved_by_lts_non_blocking_action; eauto.
Qed.

Lemma lts_input_preserved_by_cowt_output `{gLtsOba P A} p q s μ :
  Forall co_non_blocking s -> Forall (fun a => forall ν, dual ν a -> ν <> μ) s
    -> p ↛ -> (exists t, p ⟶[μ] t) -> p ⟹ᶜᵒ[s] q
      -> (exists t, q ⟶[μ] t).
Proof.
  intros s_spec1 s_spec2 hst_tau hst_inp hw.
  induction hw; eauto.
  - exfalso. eapply lts_refuses_spec2; eauto.
  - inversion s_spec1; inversion s_spec2; subst.
    eapply IHhw.
    + eassumption.
    + eassumption.
    + eapply refuses_tau_preserved_by_lts_non_blocking_action; eauto.
    + eapply lts_different_action_preserved_by_lts_non_blocking_action; eauto.
      intro heq. apply (H7 μ' duo). symmetry. exact heq.
Qed.

Lemma delay_cowt_non_blocking_action_nil `{gLtsOba P A} {p q r η} :
  non_blocking η -> p ⟶⋍[η] q -> q ⟹ᶜᵒ r
    -> exists t, p ⟹ᶜᵒ t /\ t ⟶⋍[η] r.
Proof.
  intros nb l w.
  remember ([] : trace A) as s0 eqn:Hs.
  revert p η nb l Hs.
  induction w as [ x | s1 x y z lt w IH | μ μ' s1 x y z duo lt w IH ];
    intros p0 η nb (p' & hl & heq) Hs.
  - exists p0. split; [eapply cowt_nil |].
    exists p'. split; [exact hl | exact heq].
  - assert (p' ⟶⋍ y) as (r0 & hlr & heqr).
    { eapply eq_spec. exists x. split; [exact heq | exact lt]. }
    destruct (nb_delay nb hl hlr) as (r' & l1 & (t' & l2 & heqt')).
    destruct (IH r' η nb
                (ex_intro _ t' (conj l2 (transitivity heqt' heqr))) Hs)
      as (r1 & w1 & sc).
    exists r1. split; [eapply cowt_tau; [exact l1 | exact w1] | exact sc].
  - discriminate.
Qed.

Lemma delay_cowt_non_blocking_action `{gLtsOba P A} {p q r η s} :
  non_blocking η -> p ⟶⋍[η] q -> q ⟹ᶜᵒ[s] r
    -> exists t, p ⟹ᶜᵒ[s] t /\ t ⟶⋍[η] r.
Proof.
  revert p q r η.
  induction s as [|μ s']; intros p q r η nb l w.
  - eapply delay_cowt_non_blocking_action_nil; eauto.
  - eapply cowt_pop in w as (q' & w0 & w1).
    destruct (cowt_decomp_one w0) as (q0 & q1 & μ0' & w2 & duo & l' & w3).
    destruct (delay_cowt_non_blocking_action_nil nb l w2) as (t & w4 & (q0'' & l1' & heq')).
    assert (q0'' ⟶⋍[μ0'] q1) as (r' & hr' & heqr').
    { eapply eq_spec; eauto. }
    destruct (nb_delay nb l1' hr') as (u & l2 & l3).
    edestruct (eq_spec_cowt q1 r' (symmetry heqr') r) as (t1 & w5 & l4); eauto with mdb.
    eapply cowt_push_nil_left; eassumption.
    edestruct (IHs' u r') as (t2 & w6 & l5); eauto with mdb.
    exists t2. split.
    eapply cowt_push_left. eapply cowt_push_nil_left. exact w4. eapply lts_to_cowt. exact duo. exact l2. exact w6.
    destruct l5 as (t1' & hlt1' & heqt1'). exists t1'. split; eauto with mdb.
    etrans; eassumption.
Qed.

(** *** Properties talking about [dual] in [WeakTransitions.v], restated using [cowt]

    [forward_s] already reasons about a trace dual to a process's moves via
    [Forall2 dual]; phrased with [cowt] it becomes "doing [s] then co-doing
    [s] returns (up to bisimulation) to where we started". *)

Lemma cowt_forward_s `{gLtsObaFW P A} p s :
  Forall exist_co_nba s -> exists t, p ⟹[s] t /\ t ⟹ᶜᵒ⋍[s] p.
Proof.
  intro his. eapply EquivDef in his as (s3 & nbs3 & duos3).
  destruct (forward_s p s s3 nbs3 duos3) as (t & w1 & w2).
  exists t. split; [assumption|].
  destruct w2 as (t' & hw & heq).
  exists t'. split; [| assumption].
  eapply wt_to_cowt_dual; eauto.
Qed.

(* [wt_annhil] needs a *specific* dual action of [μ] to be non-blocking; for
   [cowt], that action is whichever one the given co-step actually took, which
   [cowt_decomp_one] exposes existentially. *)
Lemma cowt_annhil `{gLtsObaFW P A} p q μ r :
  co_non_blocking μ -> p ⟹ᶜᵒ{μ} q -> q ⟹{μ} r -> p ⟹⋍ r.
Proof.
  intros nb wco w.
  eapply cowt_decomp_one in wco as (r1 & r2 & μ' & w1 & duo & l & w2).
  eapply cowt_to_wt_dual in w1 as (s1 & hf1 & w1').
  inversion hf1; subst.
  assert (r2 ⟹ q) as w2'.
  { eapply cowt_to_wt_dual in w2 as (s2 & hf2 & w2'). inversion hf2; subst. exact w2'. }
  assert (h : p ⟹[[μ'; μ]] r).
  { eapply wt_push_nil_left. exact w1'.
    eapply wt_act. exact l.
    eapply wt_push_nil_left. exact w2'. exact w. }
  apply (wt_annhil p r μ' μ (nb μ' duo)). symmetry. exact duo. exact h.
Qed.

Lemma cowt_non_blocking_action_swap `{gLtsObaFW P A} p q η1 η2 :
  co_non_blocking η1 -> co_non_blocking η2 -> p ⟹ᶜᵒ[[η1 ; η2]] q
    -> p ⟹ᶜᵒ⋍[[η2; η1]] q.
Proof.
  intros nb1 nb2 w.
  eapply cowt_to_wt_dual in w as (s' & hf & w').
  inversion hf as [| x1 y1 la1 lb1 dxy1 hf1]; subst.
  inversion hf1 as [| x2 y2 la2 lb2 dxy2 hf2]; subst.
  inversion hf2; subst.
  destruct (wt_non_blocking_action_swap p q y1 y2 (nb1 y1 (symmetry dxy1)) (nb2 y2 (symmetry dxy2)) w') as (q' & w'' & heq).
  exists q'. split; [| exact heq].
  eapply wt_to_cowt_dual. exact w''.
  constructor. exact dxy2. constructor. exact dxy1. constructor.
Qed.

Lemma cowt_input_swap `{gLtsObaFW P A} p q μ1 μ2 :
  (exists η2, non_blocking η2 /\ (forall ν, dual ν μ2 -> dual ν η2)) -> p ⟹ᶜᵒ[[μ1 ; μ2]] q
    -> p ⟹ᶜᵒ⋍[[μ2; μ1]] q.
Proof.
  intros BlocDuo w.
  eapply cowt_to_wt_dual in w as (s' & hf & w').
  inversion hf as [| x1 y1 la1 lb1 dxy1 hf1]; subst.
  inversion hf1 as [| x2 y2 la2 lb2 dxy2 hf2]; subst.
  inversion hf2; subst.
  destruct BlocDuo as (η2 & nb & hη2).
  assert (BlocDuo' : exists η2, non_blocking η2 /\ dual y2 η2).
  { exists η2. split. assumption. apply hη2. symmetry. exact dxy2. }
  destruct (wt_input_swap p q y1 y2 BlocDuo' w') as (q' & w'' & heq).
  exists q'. split; [| exact heq].
  eapply wt_to_cowt_dual. exact w''.
  constructor. exact dxy2. constructor. exact dxy1. constructor.
Qed.

Lemma Forall2_dual_perm `{ExtAction A} s1 s2 s1' :
  s1 ≡ₚ s2 -> Forall2 dual s1 s1' -> exists s2', s1' ≡ₚ s2' /\ Forall2 dual s2 s2'.
Proof.
  intro hp. revert s1'.
  induction hp; intros s1' hf.
  - inversion hf; subst. exists []. split; constructor.
  - inversion hf as [| a b la lb dab hrest]; subst.
    destruct (IHhp lb hrest) as (s2' & hp2 & hf2).
    exists (b :: s2'). split; constructor; assumption.
  - inversion hf as [| a b la lb dab hf1]; subst.
    inversion hf1 as [| a2 b2 la2 lb2 dab2 hf2]; subst.
    exists (b2 :: b :: lb2). split.
    + constructor.
    + constructor; [assumption | constructor; assumption].
  - destruct (IHhp1 s1' hf) as (s2' & hpa & hfa).
    destruct (IHhp2 s2' hfa) as (s3' & hpb & hfb).
    exists s3'. split; [etransitivity; eassumption | assumption].
Qed.

Lemma Forall_non_blocking_of_dual `{ExtAction A} s s' :
  Forall co_non_blocking s -> Forall2 dual s s' -> Forall non_blocking s'.
Proof.
  intros hcnb hf. induction hf as [| x y l l' dxy hf' IH].
  - constructor.
  - inversion hcnb as [| a b Ha Hl]; subst.
    constructor; [apply Ha; symmetry; exact dxy | apply IH; exact Hl].
Qed.

Lemma cowt_non_blocking_action_perm `{gLtsObaFW P A} {p q} s1 s2 :
  Forall co_non_blocking s1 -> s1 ≡ₚ s2 -> p ⟹ᶜᵒ[s1] q
    -> p ⟹ᶜᵒ⋍[s2] q.
Proof.
  intros hos hp w.
  eapply cowt_to_wt_dual in w as (s1' & hf1 & w1).
  destruct (Forall2_dual_perm s1 s2 s1' hp hf1) as (s2' & hp' & hf2).
  destruct (wt_non_blocking_action_perm s1' s2' (Forall_non_blocking_of_dual s1 s1' hos hf1) hp' w1)
    as (q' & w' & heq).
  exists q'. split; [| exact heq].
  eapply wt_to_cowt_dual; eauto.
Qed.

Lemma push_cowt_non_blocking_action `{gLtsObaFW P A} {p q η s} :
  co_non_blocking η -> p ⟹ᶜᵒ[η :: s] q
    -> p ⟹ᶜᵒ⋍[s ++ [η]] q.
Proof.
  intros nb w.
  eapply cowt_to_wt_dual in w as (s' & hf & w').
  inversion hf as [| x y la lb dxy hf']; subst.
  destruct (push_wt_non_blocking_action (nb y (symmetry dxy)) w') as (q' & w'' & heq).
  exists q'. split; [| exact heq].
  eapply wt_to_cowt_dual. exact w''.
  eapply Forall2_app. exact hf'. constructor. exact dxy. constructor.
Qed.

Lemma cowt_input_perm `{gLtsObaFW P A} {p q} s1 s2 :
  Forall (fun β => exists η2, non_blocking η2 /\ (forall ν, dual ν β -> dual ν η2)) s1 -> s1 ≡ₚ s2
    -> p ⟹ᶜᵒ[s1] q
    -> p ⟹ᶜᵒ⋍[s2] q.
Proof.
  intros his hp w.
  eapply cowt_to_wt_dual in w as (s1' & hf1 & w1).
  destruct (Forall2_dual_perm s1 s2 s1' hp hf1) as (s2' & hp' & hf2).
  assert (his1' : Forall exist_co_nba s1').
  { clear -his hf1. revert his. induction hf1 as [| x y la lb dxy hf' IH]; intro his.
    - constructor.
    - inversion his as [| a b Ha Hl]; subst.
      destruct Ha as (η2 & nb & hab).
      constructor.
      + exists η2. split. assumption. apply hab. symmetry. exact dxy.
      + apply IH. exact Hl. }
  destruct (wt_input_perm s1' s2' his1' hp' w1) as (q' & w' & heq).
  exists q'. split; [| exact heq].
  eapply wt_to_cowt_dual; eauto.
Qed.
