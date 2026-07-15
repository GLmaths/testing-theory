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
From Stdlib.Program Require Import Equality.
From stdpp Require Import finite gmap gmultiset.
From TestingTheory Require Import InListPropHelper ActTau gLts Bisimulation Termination
  WeakTransitions Convergence Lts_OBA_FB FiniteImageLTS coWeakTransition coConvergence.

(** ** Co-Finite Image LTSs

    [coFiniteImagegLts] supplies, for every external action [α], finiteness of
    the set of states reachable by *some* action dual to [α] — exactly the
    ingredient needed to enumerate one [cowt] step. It supplements
    [FiniteImagegLts] (still used for the plain, tau-only reachability that
    [cowt]'s nil case shares with [wt]) rather than replacing it. *)
(* [dsig] needs a [Decision] instance for the predicate it packages. Rather
   than deriving one from the canonical co-action / [unique_nb] (which would
   smuggle that machinery back in), we follow the same style as [gLts]'s own
   [lts_step_decidable] and [Prop_of_Inter]'s [inter_dec]
   (InteractionBetweenLts.v): decidability of the atomic relation the class
   is built on is simply *postulated* as a field, to be discharged by whoever
   instantiates the class for a concrete LTS. *)
Class coFiniteImagegLts P A `{gLts P A} :=
  MkCoFlts {
      cofolts_states_countable: Countable P;
      cofolts_next_states_decidable p α q : Decision (exists α', dual α' α /\ p ⟶[α'] q);
      cofolts_next_states_finite p α : Finite (dsig (fun q => exists α', dual α' α /\ p ⟶[α'] q));
}.

#[global] Existing Instance cofolts_next_states_decidable.

(* [cofolts_states_countable] is deliberately *not* registered as a global
   instance: every lemma below also carries [FiniteImagegLts P A] in scope,
   which already supplies a [Countable P] instance ([folts_states_countable]);
   registering a second, independent one here would make [gset P] resolve to
   two non-judgmentally-equal instances and break unification. *)
#[global] Existing Instance cofolts_next_states_finite.

(** *** [cowt] on the empty trace is exactly [wt] on the empty trace *)

Lemma cowt_iff_wt_nil `{gLts P A} p q : p ⟹ᶜᵒ q <-> p ⟹ q.
Proof.
  split.
  - intro w. eapply cowt_to_wt_dual in w as (s' & hf & w'). inversion hf; subst. exact w'.
  - intro w. exact (wt_to_cowt_dual p [] q w [] (ForAllHelper.Forall2_nil _)).
Qed.

Definition cowt_set_nil `{FiniteImagegLts P A} (p : P) (ht : terminate p) : gset P :=
  wt_set_nil p ht.

Lemma cowt_set_nil_fin_aux `{FiniteImagegLts P A}
  (p : P) (ht : terminate p) (d : ∀ q, Decision (p ⟹ᶜᵒ q)) :
      Finite (dsig (fun q => p ⟹ᶜᵒ q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_set_nil p ht))).
  intros q Htrans%bool_decide_unpack.
  eapply elem_of_elements, wt_set_nil_spec2. eapply cowt_iff_wt_nil. exact Htrans.
Qed.

Lemma cowt_nil_set_dec `{FiniteImagegLts P A} p (ht : p ⤓) : forall q, Decision (p ⟹ᶜᵒ q).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_set_nil p ht)).
  - left. eapply cowt_iff_wt_nil. eapply (wt_set_nil_spec1 _ _ _ e).
  - right. intro w. eapply n. eapply wt_set_nil_spec2. eapply cowt_iff_wt_nil. exact w.
Qed.

Definition cowt_set_nil_fin `{FiniteImagegLts P A}
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
  `{FiniteImagegLts P A, !coFiniteImagegLts P A} (p : P)
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

Lemma cowt_set_mu_spec1 `{FiniteImagegLts P A, !coFiniteImagegLts P A}
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

Lemma cowt_set_mu_spec2 `{FiniteImagegLts P A, !coFiniteImagegLts P A}
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

Lemma cowt_mu_set_dec `{FiniteImagegLts P A, !coFiniteImagegLts P A} p μ s (hcocnv : p ⇓ᶜᵒ μ :: s) :
    forall q, Decision (p ⟹ᶜᵒ{μ} q).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_set_mu p μ s hcocnv)).
  - left. eapply (cowt_set_mu_spec1 p q μ s hcocnv e).
  - right. intro w. eapply n. now eapply cowt_set_mu_spec2.
Qed.

Lemma cowt_mu_set_fin_aux `{FiniteImagegLts P A, !coFiniteImagegLts P A}
  (p : P) μ s (hcocnv : p ⇓ᶜᵒ μ :: s) (d : ∀ q, Decision (p ⟹ᶜᵒ{μ} q)) :
    Finite (dsig (fun q => p ⟹ᶜᵒ{μ} q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_set_mu p μ s hcocnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, cowt_set_mu_spec2.
Qed.

Definition cowt_set_mu_fin `{FiniteImagegLts P A, !coFiniteImagegLts P A}
  (p : P) μ s (hcocnv : p ⇓ᶜᵒ μ :: s) : Finite (dsig (fun q => p ⟹ᶜᵒ{μ} q)) :=
  cowt_mu_set_fin_aux p μ s hcocnv (cowt_mu_set_dec p μ s hcocnv).

(** *** The set of states reachable along a whole co-weak trace *)

Fixpoint cowt_set `{FiniteImagegLts P A, !coFiniteImagegLts P A}
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

Lemma cowt_set_spec1 `{FiniteImagegLts P A, !coFiniteImagegLts P A}
  (p q : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) :
  q ∈ cowt_set p s hcocnv -> p ⟹ᶜᵒ[s] q.
Proof.
  revert p q hcocnv. induction s; intros p q hcocnv mem; simpl in *.
  - eapply cowt_iff_wt_nil. eapply wt_set_nil_spec1. eassumption.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    eapply cowt_push_left. eapply bool_decide_unpack. eassumption.
    eapply IHs. eassumption.
Defined.

Lemma cowt_set_spec2 `{FiniteImagegLts P A, !coFiniteImagegLts P A}
  (p q : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) :
  p ⟹ᶜᵒ[s] q -> q ∈ cowt_set p s hcocnv.
Proof.
  revert p q hcocnv.
  induction s as [|μ s']; intros p q hcocnv w; simpl in *.
  - eapply wt_set_nil_spec2. eapply cowt_iff_wt_nil. eauto with mdb.
  - eapply cowt_pop in w as (t & w1 & w2).
    eapply elem_of_union_list.
    eexists. split.
    + eapply list_elem_of_fmap.
      exists (dexist t w1). now split; [|eapply elem_of_enum].
    + now eapply IHs'.
Defined.

Lemma cowt_set_dec `{FiniteImagegLts P A, !coFiniteImagegLts P A} p s (hcocnv : p ⇓ᶜᵒ s) :
    forall q, Decision (p ⟹ᶜᵒ[s] q).
Proof.
  intro q.
  destruct (decide (q ∈ cowt_set p s hcocnv)).
  - left. eapply (cowt_set_spec1 p q s hcocnv e).
  - right. intro w. eapply n. now eapply cowt_set_spec2.
Qed.

Lemma cowt_set_fin_aux `{FiniteImagegLts P A, !coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) (d : ∀ q, Decision (p ⟹ᶜᵒ[s] q)) :
    Finite (dsig (fun q => p ⟹ᶜᵒ[s] q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (cowt_set p s hcocnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, cowt_set_spec2.
Qed.

Definition cowt_set_fin `{FiniteImagegLts P A, !coFiniteImagegLts P A}
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) : Finite (dsig (fun q => p ⟹ᶜᵒ[s] q)) :=
  cowt_set_fin_aux p s hcocnv (cowt_set_dec p s hcocnv).
