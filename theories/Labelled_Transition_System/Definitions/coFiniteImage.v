(*
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
From Stdlib.Program Require Import Equality.
From stdpp Require Import finite gmap gmultiset.
From TestingTheory Require Import InListPropHelper ActTau gLts Bisimulation Termination
  WeakTransitions Convergence Lts_OBA_FB FiniteImageLTS coWeakTransition coConvergence
  StateTransitionSystems.

(** ** Co-Finite Image LTSs

    [coFiniteImagegLts] supplies, for every external action [α], finiteness of
    the set of states reachable by *some* action dual to [α] — exactly the
    ingredient needed to enumerate one [cowt] step — plus, natively (not by
    embedding [FiniteImagegLts]), [Countable P] and finiteness of plain
    tau-successors, which is all [cowt]'s nil case actually needs (it
    coincides with [wt]'s nil case, [cowt_iff_wt_nil]). This makes the class
    fully self-sufficient: `!coFiniteImagegLts P A` alone is enough
    everywhere below, [FiniteImagegLts P A] is never required as a sibling,
    and there is only ever *one* [Countable P] instance in scope — no risk of
    it resolving to two non-judgmentally-equal [gset P] types the way an
    independently-supplied [FiniteImagegLts P A] sibling could. *)
(* [dsig] needs a [Decision] instance for the predicate it packages. Rather
   than deriving one from the canonical co-action / [unique_nb] (which would
   smuggle that machinery back in), we follow the same style as [gLts]'s own
   [lts_step_decidable] and [Prop_of_Inter]'s [inter_dec]
   (InteractionBetweenLts.v): decidability of the atomic relation the class
   is built on is simply *postulated* as a field, to be discharged by whoever
   instantiates the class for a concrete LTS. *)
Class coFiniteImagegLts P A `{gLts P A} :=
  MkCoFlts {
      cofolts_states_countable :: Countable P;
      cofolts_tau_next_states_finite p : Finite (dsig (fun q => p ⟶ q));
      cofolts_next_states_decidable p α q : Decision (exists α', dual α' α /\ p ⟶[α'] q);
      cofolts_next_states_finite p α : Finite (dsig (fun q => exists α', dual α' α /\ p ⟶[α'] q));
}.

#[global] Existing Instance cofolts_states_countable.
#[global] Existing Instance cofolts_tau_next_states_finite.
#[global] Existing Instance cofolts_next_states_decidable.
#[global] Existing Instance cofolts_next_states_finite.

(** *** [coFiniteImagegLts] implies [CountablegLts] — mirrors
    [FiniteImageLTS.v]'s [finite_countable_lts] ([FiniteImagegLts P A ->
    CountablegLts P A]), sourced from [coFiniteImagegLts] instead: this is
    what lets a bare [!coFiniteImagegLts P A] context satisfy
    [StateTransitionSystems.CountableSts]/[Bar.v]'s bar-induction
    machinery (via [csts_of_clts]), without needing the (structurally
    unavailable, on the co side) full [FiniteImagegLts P A].

    The literal-[α] successor set [{q | p⟶[α]q}] isn't itself one of
    [coFiniteImagegLts]'s fields (only the *dual*-image at [α] is), but it
    embeds into the dual-image at [co α]: any [q] with [p⟶[α]q] witnesses
    membership there via [dual α (co α)] ([exists_dual] alone — no
    [unique_nb] needed), and that dual-image set *is* [Finite]
    ([cofolts_next_states_finite]) —
    hence the literal set is too, as a decidable subtype of a finite type,
    and [Finite -> Countable] ([finite_countable]) finishes it off. *)
#[global] Instance CountablegLts_of_coFiniteImagegLts `{coFiniteImagegLts P A} : CountablegLts P A.
Proof.
  unshelve econstructor.
  - exact cofolts_states_countable.
  - intros p ℓ. destruct ℓ as [a|].
    + unshelve eapply finite_countable.
      eapply (in_list_finite (map proj1_sig (enum (dsig (fun q => exists α', dual α' (co a) /\ p ⟶[α'] q))))).
      intros q Hq. eapply bool_decide_unpack in Hq.
      eapply list_elem_of_fmap.
      exists (dexist q (ex_intro _ a (conj (proj2_sig (exists_dual a)) Hq))).
      split; [reflexivity | eapply elem_of_enum].
    + apply finite_countable.
Defined.

(** *** Tau-set

    Mirrors [lts_tau_set]/[lts_tau_set_spec] (FiniteImageLTS.v) verbatim,
    sourced from [coFiniteImagegLts]'s [cofolts_tau_next_states_finite]
    instead of [FiniteImagegLts]. *)
Definition cowt_tau_set `{coFiniteImagegLts P A} p : list P :=
  map proj1_sig (enum $ dsig (fun p' => p ⟶ p')).

Lemma cowt_tau_set_spec : forall `{coFiniteImagegLts P A} p q, q ∈ cowt_tau_set p <-> p ⟶ q.
Proof.
  intros. split.
  - intro mem. unfold cowt_tau_set in mem.
    eapply list_elem_of_fmap_1 in mem as ((r & l) & eq & mem). subst.
    eapply bool_decide_unpack. simpl. eassumption.
  - intro H2. eapply list_elem_of_fmap.
    exists (dexist q H2). split.
    eauto. eapply elem_of_enum.
Qed.

(** *** Tau-successors of a whole *set*

    Mirrors [lts_tau_set_from_pset]/[_ispec] (FiniteImageLTS.v) verbatim,
    sourced from [cowt_tau_set] (hence [coFiniteImagegLts]'s own
    [cofolts_tau_next_states_finite]) instead of [FiniteImagegLts]/
    [lts_tau_set]. Lets any [!coFiniteImagegLts P A]-only context build the
    SET-level internal-reduction machinery natively, with no need to derive
    [FiniteImagegLts P A] (and hence route through
    [FiniteImageLTS.finite_countable_lts]/[StateTransitionSystems]) just
    for the tau-only part — the [lts_tau_set_from_pset_spec]/[spec1]/
    [spec2] statements themselves are already generic (bare [Countable P]),
    so no new spec vocabulary is needed either. *)
Definition cowt_tau_set_from_pset `{coFiniteImagegLts P A} (ps : gset P) : gset P :=
  ⋃ (map (fun p => list_to_set (cowt_tau_set p)) (elements ps)).

Lemma cowt_tau_set_from_pset_ispec `{coFiniteImagegLts P A}
  (ps : gset P) :
  lts_tau_set_from_pset_spec ps (cowt_tau_set_from_pset ps).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as (p & heq0 & mem1).
    subst.  eapply elem_of_list_to_set in mem2.
    eapply cowt_tau_set_spec in mem2. multiset_solver.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (cowt_tau_set p)).
    split.
    + multiset_solver.
    + eapply cowt_tau_set_spec in l. multiset_solver.
Qed.

(** *** [cowt] on the empty trace is exactly [wt] on the empty trace *)

Lemma cowt_iff_wt_nil `{gLts P A} p q : p ⟹ᶜᵒ q <-> p ⟹ q.
Proof.
  split.
  - intro w. eapply cowt_to_wt_dual in w as (s' & hf & w'). inversion hf; subst. exact w'.
  - intro w. exact (wt_to_cowt_dual p [] q w [] (ForAllHelper.Forall2_nil _)).
Qed.

(* Mirrors [wt_set_nil] (FiniteImageLTS.v) verbatim, sourced from
   [coFiniteImagegLts]'s own [cofolts_tau_next_states_finite]/
   [cofolts_states_countable] fields instead of [FiniteImagegLts], so this
   cluster never needs [FiniteImagegLts P A] as a sibling assumption. *)
Fixpoint cowt_set_nil `{coFiniteImagegLts P A} (p : P) (t : terminate p) : gset P :=
  let '(tstep _ f) := t in
  let k q := cowt_set_nil (`q) (f (`q) (proj2_dsig q)) in
  {[ p ]} ∪ ⋃ map k (enum $ dsig (fun x => p ⟶ x)).

Lemma cowt_set_nil_spec1 `{coFiniteImagegLts P A} p q (tp : terminate p) :
  q ∈ cowt_set_nil p tp -> p ⟹ᶜᵒ q.
Proof.
  intro mem. eapply cowt_iff_wt_nil.
  revert q mem.
  case tp. induction tp as [p H1 H2].
  intros t q mem. simpl in mem.
  eapply elem_of_union in mem as [here | there].
  + eapply elem_of_singleton_1 in here. subst. eauto with mdb.
  + eapply elem_of_union_list in there as (ps & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as (r & mem1 & eq). subst.
    eapply wt_tau; [|destruct (t (`r) (proj2_dsig r)) eqn:eqn0].
    ++ eapply (proj2_dsig r).
    ++ eapply H2. eapply (proj2_dsig r). eassumption.
Qed.

Lemma cowt_set_nil_spec2 `{coFiniteImagegLts P A} p q :
    forall (tp : terminate p), p ⟹ᶜᵒ q -> q ∈ cowt_set_nil p tp.
Proof.
  intros tp Htp%cowt_iff_wt_nil. revert tp. dependent induction Htp; intros tp; destruct tp.
  + set_solver.
  + eapply elem_of_union. right.
    eapply elem_of_union_list.
    set (qr := dexist q l).
    exists (cowt_set_nil (`qr) (t0 (`qr) (proj2_dsig qr))).
    split. eapply list_elem_of_fmap.
    exists qr. split. reflexivity.
    eapply elem_of_enum. simpl.
    eapply IHHtp. eauto.
Qed.

Lemma cowt_nil_set_dec `{coFiniteImagegLts P A} p (ht : p ⤓) : forall q, Decision (p ⟹ᶜᵒ q).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_set_nil p ht)).
  - left. eapply (cowt_set_nil_spec1 _ _ _ e).
  - right. intro w. eapply n. eapply cowt_set_nil_spec2. exact w.
Qed.

Lemma cowt_set_nil_fin_aux `{coFiniteImagegLts P A}
  (p : P) (ht : terminate p) (d : ∀ q, Decision (p ⟹ᶜᵒ q)) :
      Finite (dsig (fun q => p ⟹ᶜᵒ q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_set_nil p ht))).
  intros q Htrans%bool_decide_unpack.
  eapply elem_of_elements, cowt_set_nil_spec2. exact Htrans.
Qed.

Definition cowt_set_nil_fin `{coFiniteImagegLts P A}
  (p : P) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ᶜᵒ q)) :=
  cowt_set_nil_fin_aux p ht (cowt_nil_set_dec p ht).

(** *** The set of states reachable by a single co-weak action *)

Definition cowt_extaction_set `{coFiniteImagegLts P A} p μ : list P :=
  map proj1_sig (enum $ dsig (fun q => exists μ', dual μ' μ /\ p ⟶[μ'] q)).

Lemma cowt_extaction_set_spec `{coFiniteImagegLts P A} p μ q :
  q ∈ cowt_extaction_set p μ <-> exists μ', dual μ' μ /\ p ⟶[μ'] q.
Proof.
  unfold cowt_extaction_set. split.
  - intro mem. eapply list_elem_of_fmap in mem as ((r & l) & eq & mem). subst.
    eapply bool_decide_unpack. eassumption.
  - intro Hμ. eapply list_elem_of_fmap.
    eexists (dexist q Hμ). split.
    eauto. eapply elem_of_enum.
Qed.

Lemma cowt_push_nil_left_lts `{gLts P A} {p q r μ} :
  p ⟹ᶜᵒ q -> (exists μ', dual μ' μ /\ q ⟶[μ'] r) -> p ⟹ᶜᵒ{μ} r.
Proof. intros w (μ' & duo & l). eapply cowt_push_nil_left; eauto. eapply lts_to_cowt; eauto. Qed.

Definition cowt_set_mu
  `{coFiniteImagegLts P A} (p : P)
  (μ : A) (s : trace A) (hcocnv : p ⇓ᶜᵒ μ :: s) : gset P :=
  let ht := cocnv_terminate p (μ :: s) hcocnv in
  let ps0 := @enum (dsig (fun q => p ⟹ᶜᵒ q)) _ (cowt_set_nil_fin p ht) in
  let f p : list (dsig (fun x => exists μ', dual μ' μ /\ p ⟶[μ'] x)) :=
    enum (dsig (fun x => exists μ', dual μ' μ /\ p ⟶[μ'] x)) in
  ⋃ map (fun t : dsig (fun q => p ⟹ᶜᵒ q) =>
           ⋃ map (fun r : dsig (fun x => exists μ', dual μ' μ /\ (`t) ⟶[μ'] x) =>
                    let w := cowt_push_nil_left_lts (proj2_dsig t) (proj2_dsig r) in
                    let hcocnv' := cocnv_preserved_by_cowt_act s p μ hcocnv (`r) w in
                    let htr := cocnv_terminate (`r) s hcocnv' in
                    let ts := @enum (dsig (fun q => (`r) ⟹ᶜᵒ q)) _ (cowt_set_nil_fin (`r) htr) in
                    list_to_set (map (fun t => (`t)) ts)
             ) (f (`t))
    ) ps0.

Lemma cowt_set_mu_spec1 `{coFiniteImagegLts P A}
  (p q : P) (μ : A) (s : trace A) (hcocnv : p ⇓ᶜᵒ μ :: s) :
  q ∈ cowt_set_mu p μ s hcocnv -> p ⟹ᶜᵒ{μ} q.
Proof.
  intros mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply list_elem_of_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  eapply elem_of_union_list in mem2 as (g & mem3 & mem4).
  eapply list_elem_of_fmap in mem3 as ((u & hlts) & eq & mem3). subst.
  eapply elem_of_list_to_set, list_elem_of_fmap in mem4 as ((v & hw2) & eq & mem4). subst.
  simpl.
  eapply cowt_push_nil_left. eapply bool_decide_unpack. eassumption.
  eapply cowt_push_nil_right.
  eapply cowt_push_nil_left_lts. eapply cowt_nil. eapply bool_decide_unpack. eassumption.
  eapply bool_decide_unpack. eassumption.
Qed.

Lemma cowt_set_mu_spec2 `{coFiniteImagegLts P A}
  (p q : P) (μ : A) (s : trace A) (hcocnv : p ⇓ᶜᵒ μ :: s) :
  p ⟹ᶜᵒ{μ} q -> q ∈ cowt_set_mu p μ s hcocnv.
Proof.
  intros w.
  eapply cowt_decomp_one in w as (p0 & p1 & μ' & hw1 & duo & hlts & hw2).
  eapply elem_of_union_list. eexists. split.
  eapply list_elem_of_fmap. exists (dexist p0 hw1). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_union_list. eexists. split.
  eapply list_elem_of_fmap. exists (dexist p1 (ex_intro _ μ' (conj duo hlts))). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_list_to_set, list_elem_of_fmap.
  exists (dexist q hw2). split. reflexivity. eapply elem_of_enum.
Qed.

Lemma cowt_mu_set_dec `{coFiniteImagegLts P A} p μ s (hcocnv : p ⇓ᶜᵒ μ :: s) :
    forall q, Decision (p ⟹ᶜᵒ{μ} q).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_set_mu p μ s hcocnv)).
  - left. eapply (cowt_set_mu_spec1 p q μ s hcocnv e).
  - right. intro w. eapply n. now eapply cowt_set_mu_spec2.
Qed.

Lemma cowt_mu_set_fin_aux `{coFiniteImagegLts P A}
  (p : P) μ s (hcocnv : p ⇓ᶜᵒ μ :: s) (d : ∀ q, Decision (p ⟹ᶜᵒ{μ} q)) :
    Finite (dsig (fun q => p ⟹ᶜᵒ{μ} q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_set_mu p μ s hcocnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, cowt_set_mu_spec2.
Qed.

Definition cowt_set_mu_fin `{coFiniteImagegLts P A}
  (p : P) μ s (hcocnv : p ⇓ᶜᵒ μ :: s) : Finite (dsig (fun q => p ⟹ᶜᵒ{μ} q)) :=
  cowt_mu_set_fin_aux p μ s hcocnv (cowt_mu_set_dec p μ s hcocnv).

(** *** The set of states reachable along a whole co-weak trace *)

Fixpoint cowt_set `{coFiniteImagegLts P A}
  (p : P) (s : trace A) (hcocnv : cocnv p s) : gset P :=
  match s as s0 return cocnv p s0 -> gset P with
  | [] =>
      fun _ => cowt_set_nil p (cocnv_terminate p _ hcocnv)
  | μ :: s' =>
      fun f =>
        let ts := @enum (dsig (fun q => p ⟹ᶜᵒ{μ} q)) _ (cowt_set_mu_fin p μ s' f) in
        ⋃ map (fun t =>
                 let hcocnv := cocnv_preserved_by_cowt_act s' p μ f (`t) (proj2_dsig t) in
                 cowt_set (`t) s' hcocnv
          ) ts
  end hcocnv.

Lemma cowt_set_spec1 `{coFiniteImagegLts P A}
  (p q : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) :
  q ∈ cowt_set p s hcocnv -> p ⟹ᶜᵒ[s] q.
Proof.
  revert p q hcocnv. induction s; intros p q hcocnv mem; simpl in *.
  - eapply cowt_set_nil_spec1. eassumption.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    eapply cowt_push_left. eapply bool_decide_unpack. eassumption.
    eapply IHs. eassumption.
Defined.

Lemma cowt_set_spec2 `{coFiniteImagegLts P A}
  (p q : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) :
  p ⟹ᶜᵒ[s] q -> q ∈ cowt_set p s hcocnv.
Proof.
  revert p q hcocnv.
  induction s as [|μ s']; intros p q hcocnv w; simpl in *.
  - eapply cowt_set_nil_spec2. eauto with mdb.
  - eapply cowt_pop in w as (t & w1 & w2).
    eapply elem_of_union_list.
    eexists. split.
    + eapply list_elem_of_fmap.
      exists (dexist t w1). now split; [|eapply elem_of_enum].
    + now eapply IHs'.
Defined.

Lemma cowt_set_dec `{coFiniteImagegLts P A} p s (hcocnv : p ⇓ᶜᵒ s) :
    forall q, Decision (p ⟹ᶜᵒ[s] q).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_set p s hcocnv)).
  - left. eapply (cowt_set_spec1 p q s hcocnv e).
  - right. intro w. eapply n. now eapply cowt_set_spec2.
Qed.

Lemma cowt_set_fin_aux `{coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) (d : ∀ q, Decision (p ⟹ᶜᵒ[s] q)) :
    Finite (dsig (fun q => p ⟹ᶜᵒ[s] q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_set p s hcocnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, cowt_set_spec2.
Qed.

Definition cowt_set_fin `{coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) : Finite (dsig (fun q => p ⟹ᶜᵒ[s] q)) :=
  cowt_set_fin_aux p s hcocnv (cowt_set_dec p s hcocnv).

(** *** The set of stable states reachable along a whole co-weak trace

    Mirrors [wt_nil_refuses_set] (FiniteImageLTS.v) verbatim, sourced from
    [coFiniteImagegLts] instead of [FiniteImagegLts] — like [cowt_set_nil],
    it only needs [⟶]/[⟹]/[⤓], and [cowt]'s nil case coincides with [wt]'s
    ([cowt_iff_wt_nil]). *)

Lemma cocnv_cowt_s_terminate `{gLts P A}
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) : p ⟹ᶜᵒ[s] q -> q ⤓.
Proof. eapply cocnv_iff_prefix_terminate; eauto. Qed.

Fixpoint cowt_nil_refuses_set `{coFiniteImagegLts P A} (p : P) (ht : p ⤓) : gset P :=
  match lts_refuses_decidable p τ with
  | left  _ => {[ p ]}
  | right _ =>
      let '(tstep _ f) := ht in
      let k p := cowt_nil_refuses_set (`p) (f (`p) (proj2_dsig p)) in
      ⋃ map k (enum (dsig (fun q => p ⟶ q)))
  end.

Lemma cowt_nil_refuses_set_spec1 `{coFiniteImagegLts P A}
  (p q : P) (ht : p ⤓) :
  q ∈ cowt_nil_refuses_set p ht -> p ⟹ᶜᵒ q /\ q ↛.
Proof.
  intro mem.
  assert (p ⟹ q /\ q ↛) as [w hst].
  { revert q mem.
    case ht. induction ht as [p H1 H2].
    intros ht q mem. simpl in mem.
    case (lts_refuses_decidable p τ) in mem.
    - eapply elem_of_singleton_1 in mem. subst. eauto with mdb.
    - eapply elem_of_union_list in mem as (g & mem1 & mem2).
      eapply list_elem_of_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
      simpl in mem2. case (ht t (proj2_dsig (t ↾ hw1))) eqn:eq.
      edestruct (H2 t). now eapply bool_decide_unpack. eassumption.
      split; eauto with mdb. eapply wt_tau. eapply bool_decide_unpack.
      eassumption. eassumption. }
  split; [eapply cowt_iff_wt_nil; exact w | exact hst].
Qed.

Lemma cowt_nil_refuses_set_spec2 `{coFiniteImagegLts P A}
  (p q : P) (ht : p ⤓) :
  (p ⟹ᶜᵒ q /\ q ↛) -> q ∈ cowt_nil_refuses_set p ht.
Proof.
  intros (hw%cowt_iff_wt_nil & hst). dependent induction hw; case ht; induction ht; intros ht; simpl.
  - case (lts_refuses_decidable p τ); set_solver.
  - case (lts_refuses_decidable p τ); intro hst'.
    + exfalso. eapply (lts_refuses_spec2 p τ); eauto.
    + eapply elem_of_union_list.
      eexists. split. eapply list_elem_of_fmap.
      exists (dexist q l). split. reflexivity. eapply elem_of_enum. eapply IHhw; eauto.
Qed.

Definition cowt_refuses_set `{coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) : gset P :=
  let ps := @enum (dsig (fun q => p ⟹ᶜᵒ[s] q)) _ (cowt_set_fin p s hcocnv) in
  let k t := cowt_nil_refuses_set (`t) (cocnv_cowt_s_terminate p (`t) s hcocnv (proj2_dsig t)) in
  ⋃ map k ps.

Lemma cowt_refuses_set_spec1 `{coFiniteImagegLts P A}
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) :
  q ∈ cowt_refuses_set p s hcocnv -> p ⟹ᶜᵒ[s] q /\ q ↛.
Proof.
  intro mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply list_elem_of_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  simpl in mem2.
  eapply cowt_nil_refuses_set_spec1 in mem2.
  split. eapply cowt_push_nil_right. eapply bool_decide_unpack. eassumption.
  firstorder.
  firstorder.
Qed.

Lemma cowt_refuses_set_spec2 `{coFiniteImagegLts P A}
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) :
  (p ⟹ᶜᵒ[s] q /\ q ↛) -> q ∈ cowt_refuses_set p s hcocnv.
Proof.
  intros (hw & hst).
  eapply elem_of_union_list.
  eexists. split. eapply list_elem_of_fmap.
  exists (dexist q hw). split. reflexivity. eapply elem_of_enum.
  simpl. eapply cowt_nil_refuses_set_spec2. eauto with mdb.
Qed.

Lemma cowt_refuses_set_fin_aux `{coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) (d : ∀ q, Decision (p ⟹ᶜᵒ[s] q /\ q ↛)) :
  Finite (dsig (fun q => p ⟹ᶜᵒ[s] q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_refuses_set p s hcocnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, cowt_refuses_set_spec2.
Qed.

Lemma cowt_refuses_set_dec `{coFiniteImagegLts P A} p s (hcocnv : p ⇓ᶜᵒ s) :
  forall q, Decision (p ⟹ᶜᵒ[s] q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_refuses_set p s hcocnv)).
  - left. eapply (cowt_refuses_set_spec1 p q s hcocnv e).
  - right. intro w. eapply n. now eapply cowt_refuses_set_spec2.
Qed.

Definition cowt_refuses_set_fin `{coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) : Finite (dsig (fun q => p ⟹ᶜᵒ[s] q /\ q ↛)) :=
  cowt_refuses_set_fin_aux p s hcocnv (cowt_refuses_set_dec p s hcocnv).

Lemma cowt_nil_set_refuses `{coFiniteImagegLts P A} p hcocnv :
  lts_refuses p τ -> cowt_set p [] hcocnv = {[ p ]}.
Proof.
  intros hst.
  eapply leibniz_equiv.
  intro q. split.
  - intro mem.
    eapply cowt_set_spec1 in mem. eapply cowt_iff_wt_nil in mem.
    inversion mem; subst.
    + set_solver.
    + exfalso. eapply lts_refuses_spec2; eauto.
  - intro mem. eapply cowt_set_spec2. replace q with p.
    eapply cowt_iff_wt_nil. eauto with mdb. set_solver.
Qed.

Lemma cowt_refuses_set_refuses_singleton `{coFiniteImagegLts P A} p hcocnv :
  lts_refuses p τ -> cowt_refuses_set p [] hcocnv = {[ p ]}.
Proof.
  intro hst.
  eapply leibniz_equiv.
  intro q. split; intro mem.
  - eapply cowt_refuses_set_spec1 in mem as (w & hst').
    eapply cowt_iff_wt_nil in w.
    inversion w; subst. set_solver. exfalso. eapply lts_refuses_spec2; eauto.
  - eapply elem_of_singleton_1 in mem. subst.
    eapply cowt_refuses_set_spec2. split; eauto with mdb.
Qed.

(** *** The set of states a whole *set* [P] reaches via a single co-weak
    action — mirrors [wt_set_from_pset_spec1]/[spec2]/[spec]
    (FiniteImageLTS.v's "from_pset" section), packaging the dual directly
    into [⟹ᶜᵒ{μ}] (a single [μ], no separate [dual μ1 μ2] premise) instead of
    the two-label [wt_set_from_pset_spec1 ps [μ1] qs] + [dual μ1 μ2] style. *)

Definition cowt_set_from_pset_spec1 `{Countable P} `{gLts P A}
  (ps : gset P) (μ : A) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹ᶜᵒ{μ} q.

Definition cowt_set_from_pset_spec2 `{Countable P} `{gLts P A}
  (ps : gset P) (μ : A) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟹ᶜᵒ{μ} q -> q ∈ qs.

Definition cowt_set_from_pset_spec `{Countable P} `{gLts P A}
  (ps : gset P) (μ : A) (qs : gset P) :=
  cowt_set_from_pset_spec1 ps μ qs /\ cowt_set_from_pset_spec2 ps μ qs.

(** *** A concrete witness set for [cowt_set_from_pset_spec] — mirrors
    [wt_s_set_from_pset]/[wt_s_set_from_pset_ispec] (FiniteImageLTS.v)
    verbatim, restricted to a single action [μ] (so it is sourced from
    [cowt_set_mu] instead of the general-trace [wt_set]). *)

Fixpoint cowt_s_set_from_pset_mu_xs `{coFiniteImagegLts P A}
  (ps : list P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) : gset P :=
  match ps as ps0 return (forall p, p ∈ ps0 -> p ⇓ᶜᵒ [μ]) -> gset P with
  | [] => fun _ => ∅
  | p :: ps' =>
      fun ha =>
        let pr := ha p (list_elem_of_here p ps') in
        let ys := cowt_set_mu p μ [] pr in
        let ha' := fun q mem => ha q (list_elem_of_further q p ps' mem) in
        ys ∪ cowt_s_set_from_pset_mu_xs ps' μ ha'
  end hcocnv.

Lemma cowt_s_set_from_pset_mu_xs_ispec `{coFiniteImagegLts P A}
  (ps : list P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) :
  (forall q, q ∈ cowt_s_set_from_pset_mu_xs ps μ hcocnv -> exists p, p ∈ ps /\ p ⟹ᶜᵒ{μ} q)
  /\ (forall p q, p ∈ ps -> p ⟹ᶜᵒ{μ} q -> q ∈ cowt_s_set_from_pset_mu_xs ps μ hcocnv).
Proof.
  split.
  - induction ps as [|p ps].
    intros p mem. set_solver.
    intros p' mem. simpl in *.
    eapply elem_of_union in mem as [hl|hr].
    exists p. split.
    set_solver. now eapply cowt_set_mu_spec1 in hl.
    eapply IHps in hr as (p0 & mem & hwp0).
    exists p0. repeat split; set_solver.
  - induction ps as [|p ps].
    + intros p'. set_solver.
    + intros p' q mem hwp'.
      eapply elem_of_union.
      inversion mem; subst.
      ++ left. eapply cowt_set_mu_spec2; eauto.
      ++ right. eapply IHps in hwp'; eauto.
Qed.

Lemma lift_cocnv_elements `{coFiniteImagegLts P A}
  (ps : gset P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) :
  forall p, p ∈ (elements ps) -> p ⇓ᶜᵒ [μ].
Proof.
  intros p mem.
  eapply hcocnv. now eapply elem_of_elements.
Qed.

Definition cowt_s_set_from_pset `{coFiniteImagegLts P A}
  (ps : gset P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) : gset P :=
  cowt_s_set_from_pset_mu_xs (elements ps) μ (lift_cocnv_elements ps μ hcocnv).

Lemma cowt_s_set_from_pset_ispec `{coFiniteImagegLts P A}
  (ps : gset P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) :
  cowt_set_from_pset_spec ps μ (cowt_s_set_from_pset ps μ hcocnv).
Proof.
  split.
  - intros p mem.
    eapply cowt_s_set_from_pset_mu_xs_ispec in mem as (p' & mem & hwp').
    exists p'. split; set_solver.
  - intros p q mem hwp.
    eapply cowt_s_set_from_pset_mu_xs_ispec.
    eapply elem_of_elements; eassumption. eassumption.
Qed.
