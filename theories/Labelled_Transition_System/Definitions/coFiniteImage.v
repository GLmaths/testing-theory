(* begin hide *)
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
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality.
From stdpp Require Import finite gmap gmultiset.
From TestingTheory Require Import InListPropHelper ActTau gLts SyncActions Bisimulation Termination
  WeakTransitions Convergence Lts_OBA_FB FiniteImageLTS coWeakTransition coConvergence
  StateTransitionSystems.

(* ****** Co-Finite Image LTSs *)
Class coFiniteImagegLts (P A : Type) {Aproc : Type} {Hp : ExtAction Aproc} {gLtsP : gLts P Hp}
  {Ht : ExtAction A} {SA : SyncAction Aproc A} :=
  MkCoFlts {
      cofolts_states_countable :: Countable P;
      cofolts_tau_next_states_finite p : Finite (dsig (fun q => p ⟶ q));
      cofolts_next_states_decidable p (𝜆 : A) q : Decision (exists 𝜆', sync 𝜆' 𝜆 /\ p ⟶[𝜆'] q);
      cofolts_next_states_finite p (𝜆 : A) : Finite (dsig (fun q => exists 𝜆', sync 𝜆' 𝜆 /\ p ⟶[𝜆'] q));
}.

#[global] Existing Instance cofolts_states_countable.
#[global] Existing Instance cofolts_tau_next_states_finite.
#[global] Existing Instance cofolts_next_states_decidable.
#[global] Existing Instance cofolts_next_states_finite.

#[global] Instance CountablegLts_of_coFiniteImagegLts `{H : ExtAction A} `{gLtsP : !gLts P H}
  `{!coFiniteImagegLts P A} : CountablegLts P A.
Proof.
  unshelve econstructor.
  - exact cofolts_states_countable.
  - intros p 𝜆. destruct 𝜆 as [a|].
    + unshelve eapply finite_countable.
      eapply (in_list_finite (map proj1_sig (enum (dsig (fun q => exists 𝜆', sync 𝜆' (co a) /\ p ⟶[𝜆'] q))))).
      intros q Hq. eapply bool_decide_unpack in Hq.
      eapply list_elem_of_fmap.
      exists (dexist q (ex_intro _ a (conj (proj2_sig (exists_dual a)) Hq))).
      split; [reflexivity | eapply elem_of_enum].
    + apply finite_countable.
Defined.

Section coFiniteImage_sets.

Context `{gLtsP : @gLts P Aproc Hp} `{Ht : ExtAction A} `{SA : !SyncAction Aproc A}.
Context `{CFI : !coFiniteImagegLts P A}.

(*** ******** Tau-set *)
Definition colts_tau_set p : list P :=
  map proj1_sig (enum $ dsig (fun p' => p ⟶ p')).

Lemma colts_tau_set_spec : forall p q, q ∈ colts_tau_set p <-> p ⟶ q.
Proof.
  intros. split.
  - intro mem. unfold colts_tau_set in mem.
    eapply list_elem_of_fmap_1 in mem as ((r & l) & eq & mem). subst.
    eapply bool_decide_unpack. simpl. eassumption.
  - intro H2. eapply list_elem_of_fmap.
    exists (dexist q H2). split.
    eauto. eapply elem_of_enum.
Qed.

(** ****** Tau-successors of a whole *set* *)
Definition colts_tau_set_from_pset (ps : gset P) : gset P :=
  ⋃ (map (fun p => list_to_set (colts_tau_set p)) (elements ps)).

Lemma colts_tau_set_from_pset_ispec
  (ps : gset P) :
  lts_tau_set_from_pset_spec ps (colts_tau_set_from_pset ps).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as (p & heq0 & mem1).
    subst.  eapply elem_of_list_to_set in mem2.
    eapply colts_tau_set_spec in mem2. multiset_solver.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (colts_tau_set p)).
    split.
    + multiset_solver.
    + eapply colts_tau_set_spec in l. multiset_solver.
Qed.

(** ****** Lazily unfolded termination proofs *)

Definition terminate_next {p q : P} (t : p ⤓) (l : p ⟶ q) : q ⤓ :=
  match t with tstep _ f => f q l end.

Fixpoint terminate_guard (n : nat) {p : P} (t : p ⤓) : p ⤓ :=
  match n with
  | 0 => t
  | S n => tstep p (fun q l => terminate_guard n (terminate_next t l))
  end.

Arguments terminate_guard : simpl never.

Definition terminate_guard_depth : nat := Nat.pow 2 18.

Arguments terminate_guard_depth : simpl never.

(** ****** Depth-first τ-closure with a set of visited states *)

Lemma cowt_tau_dsig_step p (q : dsig (fun x => p ⟶ x)) : p ⟶ `q.
Proof. exact (proj2_dsig q). Qed.

Fixpoint cowt_dfs (p : P) (t : p ⤓) (vis : gset P) {struct t} : gset P :=
  if decide (p ∈ vis) then vis
  else
    let '(tstep _ f) := t in
    foldr (fun q acc => cowt_dfs (`q) (f (`q) (cowt_tau_dsig_step p q)) acc)
      ({[ p ]} ∪ vis) (enum (dsig (fun x => p ⟶ x))).

Definition cowt_dfs_inv (S vis R : gset P) : Prop :=
  vis ⊆ R ∧ S ⊆ R ∧
  (∀ x, x ∈ R → x ∉ vis → ∃ p, p ∈ S ∧ p ⟹ᶜᵒ x) ∧
  (∀ x y, x ∈ R → x ∉ vis → x ⟶ y → y ∈ R).

Lemma cowt_dfs_inv_trans S1 S2 vis R1 R :
  cowt_dfs_inv S1 vis R1 → cowt_dfs_inv S2 R1 R → cowt_dfs_inv (S1 ∪ S2) vis R.
Proof.
  intros (a1 & a2 & a3 & a4) (b1 & b2 & b3 & b4). repeat split.
  - set_solver.
  - set_solver.
  - intros x hx hn. destruct (decide (x ∈ R1)) as [h | h].
    + destruct (a3 x h hn) as (p0 & hp0 & w). exists p0. split; [set_solver | exact w].
    + destruct (b3 x hx h) as (p0 & hp0 & w). exists p0. split; [set_solver | exact w].
  - intros x y hx hn l. destruct (decide (x ∈ R1)) as [h | h].
    + apply b1. eapply a4; eauto.
    + eapply b4; eauto.
Qed.

Lemma cowt_dfs_fold p (l : list (dsig (fun x => p ⟶ x)))
  (g : dsig (fun x => p ⟶ x) → gset P → gset P) V0 :
  (∀ q acc, cowt_dfs_inv {[ `q ]} acc (g q acc)) →
  V0 ⊆ foldr g V0 l ∧ (∀ q, q ∈ l → `q ∈ foldr g V0 l) ∧
  (∀ x, x ∈ foldr g V0 l → x ∉ V0 → p ⟹ᶜᵒ x) ∧
  (∀ x y, x ∈ foldr g V0 l → x ∉ V0 → x ⟶ y → y ∈ foldr g V0 l).
Proof.
  intros hg. induction l as [|q l (a1 & a2 & a3 & a4)]; simpl.
  - repeat split.
    + set_solver.
    + intros q hq. inversion hq.
    + intros x hx hn. contradiction.
    + intros x y hx hn. contradiction.
  - destruct (hg q (foldr g V0 l)) as (b1 & b2 & b3 & b4). repeat split.
    + set_solver.
    + intros q' [-> | hq']%elem_of_cons; [set_solver |]. apply b1, a2, hq'.
    + intros x hx hn. destruct (decide (x ∈ foldr g V0 l)) as [h | h].
      * eapply a3; eauto.
      * destruct (b3 x hx h) as (p0 & ->%elem_of_singleton_1 & w).
        eapply cowt_tau; [exact (proj2_dsig q) | exact w].
    + intros x y hx hn l'. destruct (decide (x ∈ foldr g V0 l)) as [h | h].
      * apply b1. eapply a4; eauto.
      * eapply b4; eauto.
Qed.

Lemma cowt_dfs_spec p : p ⤓ → ∀ (t : p ⤓) vis, cowt_dfs_inv {[ p ]} vis (cowt_dfs p t vis).
Proof.
  intros hp. induction hp as [p _ IH]. intros [f] vis. simpl.
  case_decide as hin.
  - repeat split.
    + set_solver.
    + set_solver.
    + intros x hx hn. contradiction.
    + intros x y hx hn. contradiction.
  - match goal with
    | |- cowt_dfs_inv _ _ (foldr ?g ?V0 ?l) =>
        assert (hg : ∀ q acc, cowt_dfs_inv {[ `q ]} acc (g q acc))
          by (intros q acc; exact (IH (`q) (proj2_dsig q) _ acc));
        destruct (cowt_dfs_fold p l g V0 hg) as (h1 & h2 & h3 & h4)
    end.
    repeat split.
    + set_solver.
    + set_solver.
    + intros x hx hn. exists p. split; [set_solver |].
      destruct (decide (x = p)) as [-> | hneq]; [eauto with mdb |].
      eapply h3; [exact hx | set_solver].
    + intros x y hx hn l. destruct (decide (x = p)) as [-> | hneq].
      * apply (h2 (dexist y l)), elem_of_enum.
      * eapply h4; [exact hx | set_solver | exact l].
Qed.

Fixpoint cowt_dfs_list (G : ∀ p : P, p ⤓ → p ⤓) (ps : list P) :
    (∀ p, p ∈ ps → p ⤓) → gset P → gset P :=
  match ps as ps0 return (∀ p, p ∈ ps0 → p ⤓) → gset P → gset P with
  | [] => fun _ vis => vis
  | p :: ps' => fun ht vis =>
      cowt_dfs_list G ps' (fun q mem => ht q (list_elem_of_further q p ps' mem))
        (cowt_dfs p (G p (ht p (list_elem_of_here p ps'))) vis)
  end.

Lemma cowt_dfs_list_spec G ps : ∀ ht vis, cowt_dfs_inv (list_to_set ps) vis (cowt_dfs_list G ps ht vis).
Proof.
  induction ps as [|p ps IH]; intros ht vis; cbn [cowt_dfs_list list_to_set].
  - repeat split.
    + set_solver.
    + set_solver.
    + intros x hx hn. contradiction.
    + intros x y hx hn. contradiction.
  - eapply cowt_dfs_inv_trans; [| apply IH].
    apply cowt_dfs_spec. exact (ht p (list_elem_of_here p ps)).
Qed.

Lemma cowt_closed_nil (R : gset P) p q :
  (∀ x y, x ∈ R → x ⟶ y → y ∈ R) → p ∈ R → p ⟹ᶜᵒ q → q ∈ R.
Proof.
  intros hR hp w. remember ([] : trace A) as s0 eqn:hs0 in w. revert hs0 hp.
  induction w as [p | s0 p p' q l w IH | ]; intros hs0 hp; [done | | discriminate].
  eapply IH; [exact hs0 | eapply hR; eauto].
Qed.

(** ****** τ-closure of a set of terminating states *)

Definition cowt_closure (X : gset P) (ht : ∀ p, p ∈ X → p ⤓) : gset P :=
  let n := terminate_guard_depth in
  cowt_dfs_list (fun p t => terminate_guard n t) (elements X)
    (fun p mem => ht p (proj1 (elem_of_elements _ _) mem)) ∅.

Lemma cowt_closure_spec X ht q :
  q ∈ cowt_closure X ht ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ q.
Proof.
  unfold cowt_closure. cbv zeta.
  match goal with
  | |- context [cowt_dfs_list ?G ?l ?h ?v] =>
      destruct (cowt_dfs_list_spec G l h v) as (h1 & h2 & h3 & h4)
  end.
  split.
  - intros hq. destruct (h3 q hq (not_elem_of_empty q)) as (p & hp & w).
    exists p. split; [set_solver | exact w].
  - intros (p & hp & w). eapply cowt_closed_nil; [| | exact w].
    + intros x y hx l. eapply h4; [exact hx | apply not_elem_of_empty | exact l].
    + apply h2. set_solver.
Qed.

Lemma singleton_terminate p (ht : p ⤓) : ∀ q, q ∈ ({[ p ]} : gset P) → q ⤓.
Proof. intros q ->%elem_of_singleton_1. exact ht. Qed.

Lemma singleton_cocnv p s (h : p ⇓ᶜᵒ s) : ∀ q, q ∈ ({[ p ]} : gset P) → q ⇓ᶜᵒ s.
Proof. intros q ->%elem_of_singleton_1. exact h. Qed.

Definition cowt_set_nil (p : P) (ht : p ⤓) : gset P :=
  cowt_closure {[ p ]} (singleton_terminate p ht).

Lemma cowt_set_nil_spec p (ht : p ⤓) q : q ∈ cowt_set_nil p ht ↔ p ⟹ᶜᵒ q.
Proof.
  unfold cowt_set_nil. rewrite cowt_closure_spec. split.
  - intros (p' & ->%elem_of_singleton_1 & w). exact w.
  - intros w. exists p. split; [set_solver | exact w].
Qed.

Lemma cowt_set_nil_spec1 p q (tp : p ⤓) :
  q ∈ cowt_set_nil p tp -> p ⟹ᶜᵒ q.
Proof. apply cowt_set_nil_spec. Qed.

Lemma cowt_set_nil_spec2 p q :
    forall (tp : p ⤓), p ⟹ᶜᵒ q -> q ∈ cowt_set_nil p tp.
Proof. intros tp. apply cowt_set_nil_spec. Qed.

Definition cowt_nil_set_dec p (ht : p ⤓) : forall q, Decision (p ⟹ᶜᵒ q) :=
  gset_decision (cowt_set_nil p ht) _ (cowt_set_nil_spec p ht).

Definition cowt_set_nil_fin
  (p : P) (ht : p ⤓) : Finite (@dsig P (fun q => p ⟹ᶜᵒ q) (cowt_nil_set_dec p ht)) :=
  gset_finite (cowt_set_nil p ht) _ (cowt_set_nil_spec p ht).

(** ******* The set of states reachable by a single co-weak action *)

Definition colts_extaction_set p μ : list P :=
  map proj1_sig (enum $ dsig (fun q => exists μ', sync μ' μ /\ p ⟶[μ'] q)).

Lemma colts_extaction_set_spec p μ q :
  q ∈ colts_extaction_set p μ <-> exists μ', sync μ' μ /\ p ⟶[μ'] q.
Proof.
  unfold colts_extaction_set. split.
  - intro mem. eapply list_elem_of_fmap in mem as ((r & l) & eq & mem). subst.
    eapply bool_decide_unpack. eassumption.
  - intro Hμ. eapply list_elem_of_fmap.
    eexists (dexist q Hμ). split.
    eauto. eapply elem_of_enum.
Qed.

Lemma cowt_push_nil_left_lts {p q r μ} :
  p ⟹ᶜᵒ q -> (exists μ', sync μ' μ /\ q ⟶[μ'] r) -> p ⟹ᶜᵒ{μ} r.
Proof. intros w (μ' & duo & l). eapply cowt_push_nil_left; eauto. eapply lts_to_cowt; eauto. Qed.

(** ******* Set-level steps along a co-weak trace *)

Definition colts_extaction_set_from_pset (ps : gset P) (η : A) : gset P :=
  ⋃ (map (fun p => list_to_set (colts_extaction_set p η)) (elements ps)).

Definition colts_extaction_set_from_pset_spec1 `{CP : Countable P}
  (ps : gset P) (η : A) (qs : gset P) :=
  ∀ q, q ∈ qs → ∃ p, p ∈ ps ∧ ∃ μ, sync μ η ∧ p ⟶[μ] q.

Definition colts_extaction_set_from_pset_spec2 `{CP : Countable P}
  (ps : gset P) (η : A) (qs : gset P) :=
  ∀ p q, p ∈ ps → (∃ μ, sync μ η ∧ p ⟶[μ] q) → q ∈ qs.

Definition colts_extaction_set_from_pset_spec `{CP : Countable P}
  (ps : gset P) (η : A) (qs : gset P) :=
  colts_extaction_set_from_pset_spec1 ps η qs ∧ colts_extaction_set_from_pset_spec2 ps η qs.

Lemma colts_extaction_set_from_pset_ispec (ps : gset P) (η : A) :
  colts_extaction_set_from_pset_spec ps η (colts_extaction_set_from_pset ps η).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply list_elem_of_fmap in mem1 as (p & heq0 & mem1).
    subst. eapply elem_of_list_to_set in mem2.
    eapply colts_extaction_set_spec in mem2.
    exists p. split; eauto. eapply elem_of_elements. eauto.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (colts_extaction_set p η)).
    split.
    + eapply list_elem_of_fmap. exists p. split; eauto. eapply elem_of_elements. eauto.
    + eapply elem_of_list_to_set. eapply colts_extaction_set_spec. eauto.
Qed.

Lemma elem_of_colts_extaction_set_from_pset X μ q :
  q ∈ colts_extaction_set_from_pset X μ ↔ ∃ p, p ∈ X ∧ ∃ μ', sync μ' μ ∧ p ⟶[μ'] q.
Proof.
  unfold colts_extaction_set_from_pset. rewrite elem_of_union_list. split.
  - intros (Y & hY & hq). apply list_elem_of_fmap in hY as (p & -> & hp).
    apply elem_of_list_to_set, colts_extaction_set_spec in hq.
    exists p. split; [now apply elem_of_elements | exact hq].
  - intros (p & hp & hq). exists (list_to_set (colts_extaction_set p μ)). split.
    + apply list_elem_of_fmap. exists p. split; [done | now apply elem_of_elements].
    + apply elem_of_list_to_set, colts_extaction_set_spec, hq.
Qed.

Lemma cowt_cons_inv p q μ s :
  p ⟹ᶜᵒ[μ :: s] q → ∃ t r μ', p ⟹ᶜᵒ t ∧ sync μ' μ ∧ t ⟶[μ'] r ∧ r ⟹ᶜᵒ[s] q.
Proof.
  intro w. remember (μ :: s) as s0 eqn:hs0 in w. revert hs0.
  induction w as [p | s0 p p' q l w IH | μ0 μ0' s0 p p' q duo l w IH]; intros hs0; [discriminate | |].
  - destruct (IH hs0) as (t & r & μ' & w1 & duo & l' & w2).
    exists t, r, μ'. repeat split; eauto with mdb.
  - injection hs0 as -> ->. exists p, p', μ0'. repeat split; eauto with mdb.
Qed.

Definition cowt_after (X : gset P) μ s (h : ∀ p, p ∈ X → p ⇓ᶜᵒ μ :: s) : gset P :=
  colts_extaction_set_from_pset (cowt_closure X (fun p hp => cocnv_terminate p _ (h p hp))) μ.

Lemma cowt_after_spec X μ s h q :
  q ∈ cowt_after X μ s h ↔ ∃ p t μ', p ∈ X ∧ p ⟹ᶜᵒ t ∧ sync μ' μ ∧ t ⟶[μ'] q.
Proof.
  unfold cowt_after. rewrite elem_of_colts_extaction_set_from_pset. split.
  - intros (t & ht & μ' & duo & l). apply cowt_closure_spec in ht as (p & hp & w).
    exists p, t, μ'. repeat split; assumption.
  - intros (p & t & μ' & hp & w & duo & l). exists t. split.
    + apply cowt_closure_spec. exists p. split; assumption.
    + exists μ'. split; assumption.
Qed.

Lemma cowt_after_cocnv X μ s h q : q ∈ cowt_after X μ s h → q ⇓ᶜᵒ s.
Proof.
  intros (p & t & μ' & hp & w & duo & l)%cowt_after_spec.
  eapply (cocnv_preserved_by_cowt_act s p μ (h p hp)).
  exact (cowt_push_nil_left_lts w (ex_intro _ μ' (conj duo l))).
Qed.

Fixpoint coreachable_from (s : trace A) : ∀ X : gset P, (∀ p, p ∈ X → p ⇓ᶜᵒ s) → gset P :=
  match s as s0 return ∀ X : gset P, (∀ p, p ∈ X → p ⇓ᶜᵒ s0) → gset P with
  | [] => fun X h => cowt_closure X (fun p hp => cocnv_terminate p [] (h p hp))
  | μ :: s' => fun X h => coreachable_from s' (cowt_after X μ s' h) (cowt_after_cocnv X μ s' h)
  end.

Lemma coreachable_from_spec s : ∀ X h q,
  q ∈ coreachable_from s X h ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ[s] q.
Proof.
  induction s as [|μ s IH]; intros X h q; cbn [coreachable_from].
  - apply cowt_closure_spec.
  - rewrite IH. split.
    + intros (r & hr & w). apply cowt_after_spec in hr as (p & t & μ' & hp & w1 & duo & l).
      exists p. split; [exact hp |]. eapply cowt_push_nil_left; [exact w1 |].
      eapply cowt_act; eauto.
    + intros (p & hp & w). apply cowt_cons_inv in w as (t & r & μ' & w1 & duo & l & w2).
      exists r. split; [| exact w2].
      apply cowt_after_spec. exists p, t, μ'. repeat split; assumption.
Qed.

(** ******* The set of states reachable by a single co-weak action *)

Definition cowt_set_mu
  (p : P) (μ : A) (s : trace A) (hcocnv : p ⇓ᶜᵒ μ :: s) : gset P :=
  coreachable_from [μ] {[ p ]} (singleton_cocnv p [μ] (cocnv_wk hcocnv)).

Lemma cowt_set_mu_spec p μ s (hcocnv : p ⇓ᶜᵒ μ :: s) q :
  q ∈ cowt_set_mu p μ s hcocnv ↔ p ⟹ᶜᵒ{μ} q.
Proof.
  unfold cowt_set_mu. rewrite coreachable_from_spec. split.
  - intros (p' & ->%elem_of_singleton_1 & w). exact w.
  - intros w. exists p. split; [set_solver | exact w].
Qed.

Lemma cowt_set_mu_spec1
  (p q : P) (μ : A) (s : trace A) (hcocnv : p ⇓ᶜᵒ μ :: s) :
  q ∈ cowt_set_mu p μ s hcocnv -> p ⟹ᶜᵒ{μ} q.
Proof. apply cowt_set_mu_spec. Qed.

Lemma cowt_set_mu_spec2
  (p q : P) (μ : A) (s : trace A) (hcocnv : p ⇓ᶜᵒ μ :: s) :
  p ⟹ᶜᵒ{μ} q -> q ∈ cowt_set_mu p μ s hcocnv.
Proof. apply cowt_set_mu_spec. Qed.

Definition cowt_mu_set_dec p μ s (hcocnv : p ⇓ᶜᵒ μ :: s) :
    forall q, Decision (p ⟹ᶜᵒ{μ} q) :=
  gset_decision (cowt_set_mu p μ s hcocnv) _ (cowt_set_mu_spec p μ s hcocnv).

Definition cowt_set_mu_fin
  (p : P) μ s (hcocnv : p ⇓ᶜᵒ μ :: s) :
  Finite (@dsig P (fun q => p ⟹ᶜᵒ{μ} q) (cowt_mu_set_dec p μ s hcocnv)) :=
  gset_finite (cowt_set_mu p μ s hcocnv) _ (cowt_set_mu_spec p μ s hcocnv).

(*** ******* The set of states reachable along a whole co-weak trace *)

Definition coreachable_states
  (p : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) : gset P :=
  coreachable_from s {[ p ]} (singleton_cocnv p s hcocnv).

Lemma coreachable_states_spec p s (hcocnv : p ⇓ᶜᵒ s) q :
  q ∈ coreachable_states p s hcocnv ↔ p ⟹ᶜᵒ[s] q.
Proof.
  unfold coreachable_states. rewrite coreachable_from_spec. split.
  - intros (p' & ->%elem_of_singleton_1 & w). exact w.
  - intros w. exists p. split; [set_solver | exact w].
Qed.

Lemma coreachable_states_spec1
  (p q : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) :
  q ∈ coreachable_states p s hcocnv -> p ⟹ᶜᵒ[s] q.
Proof. apply coreachable_states_spec. Qed.

Lemma coreachable_states_spec2
  (p q : P) (s : trace A) (hcocnv : p ⇓ᶜᵒ s) :
  p ⟹ᶜᵒ[s] q -> q ∈ coreachable_states p s hcocnv.
Proof. apply coreachable_states_spec. Qed.

Definition coreachable_states_dec p s (hcocnv : p ⇓ᶜᵒ s) :
    forall q, Decision (p ⟹ᶜᵒ[s] q) :=
  gset_decision (coreachable_states p s hcocnv) _ (coreachable_states_spec p s hcocnv).

Definition coreachable_states_fin
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) : Finite (@dsig P (fun q => p ⟹ᶜᵒ[s] q) (coreachable_states_dec p s hcocnv)) :=
  gset_finite (coreachable_states p s hcocnv) _ (coreachable_states_spec p s hcocnv).

Lemma cocnv_cowt_s_terminate
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) : p ⟹ᶜᵒ[s] q -> q ⤓.
Proof. eapply cocnv_iff_prefix_terminate; eauto. Qed.

Definition cowt_nil_stable_set (p : P) (ht : p ⤓) : gset P :=
  filter (fun q => q ↛) (cowt_set_nil p ht).

Lemma cowt_nil_stable_set_spec1
  (p q : P) (ht : p ⤓) :
  q ∈ cowt_nil_stable_set p ht -> p ⟹ᶜᵒ q /\ q ↛.
Proof. intros (hst & hq)%elem_of_filter. split; [now apply cowt_set_nil_spec in hq | exact hst]. Qed.

Lemma cowt_nil_stable_set_spec2
  (p q : P) (ht : p ⤓) :
  (p ⟹ᶜᵒ q /\ q ↛) -> q ∈ cowt_nil_stable_set p ht.
Proof. intros (w & hst). apply elem_of_filter. split; [exact hst | now apply cowt_set_nil_spec]. Qed.

Definition cowaiting_states
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) : gset P :=
  filter (fun q => q ↛) (coreachable_states p s hcocnv).

Lemma cowaiting_states_spec
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) :
  q ∈ cowaiting_states p s hcocnv ↔ p ⟹ᶜᵒ[s] q /\ q ↛.
Proof.
  unfold cowaiting_states. rewrite elem_of_filter, coreachable_states_spec. tauto.
Qed.

Lemma cowaiting_states_spec1
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) :
  q ∈ cowaiting_states p s hcocnv -> p ⟹ᶜᵒ[s] q /\ q ↛.
Proof. apply cowaiting_states_spec. Qed.

Lemma cowaiting_states_spec2
  (p q : P) s (hcocnv : p ⇓ᶜᵒ s) :
  (p ⟹ᶜᵒ[s] q /\ q ↛) -> q ∈ cowaiting_states p s hcocnv.
Proof. apply cowaiting_states_spec. Qed.

Definition cowaiting_states_dec p s (hcocnv : p ⇓ᶜᵒ s) :
  forall q, Decision (p ⟹ᶜᵒ[s] q /\ q ↛) :=
  gset_decision (cowaiting_states p s hcocnv) _ (fun q => cowaiting_states_spec p q s hcocnv).

Definition cowaiting_states_fin
  (p : P) s (hcocnv : p ⇓ᶜᵒ s) :
  Finite (@dsig P (fun q => p ⟹ᶜᵒ[s] q /\ q ↛) (cowaiting_states_dec p s hcocnv)) :=
  gset_finite (cowaiting_states p s hcocnv) _ (fun q => cowaiting_states_spec p q s hcocnv).

Lemma cowt_nil_set_stable p hcocnv :
  (p ↛) -> coreachable_states p [] hcocnv = {[ p ]}.
Proof.
  intros hst.
  eapply leibniz_equiv.
  intro q. split.
  - intro mem.
    eapply coreachable_states_spec1 in mem. eapply cowt_iff_wt_nil in mem.
    inversion mem; subst.
    + set_solver.
    + exfalso. apply hst, lts_performs_spec2. eauto.
  - intro mem. eapply coreachable_states_spec2. replace q with p.
    eapply cowt_iff_wt_nil. eauto with mdb. set_solver.
Qed.

Lemma cowaiting_states_stable_singleton p hcocnv :
  (p ↛) -> cowaiting_states p [] hcocnv = {[ p ]}.
Proof.
  intro hst.
  eapply leibniz_equiv.
  intro q. split; intro mem.
  - eapply cowaiting_states_spec1 in mem as (w & hst').
    eapply cowt_iff_wt_nil in w.
    inversion w; subst. set_solver. exfalso. apply hst, lts_performs_spec2. eauto.
  - eapply elem_of_singleton_1 in mem. subst.
    eapply cowaiting_states_spec2. split; eauto with mdb.
Qed.

Definition cowt_set_from_pset_spec1 `{Countable P} 
  (ps : gset P) (μ : A) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹ᶜᵒ{μ} q.

Definition cowt_set_from_pset_spec2 `{Countable P} 
  (ps : gset P) (μ : A) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟹ᶜᵒ{μ} q -> q ∈ qs.

Definition cowt_set_from_pset_spec `{Countable P} 
  (ps : gset P) (μ : A) (qs : gset P) :=
  cowt_set_from_pset_spec1 ps μ qs /\ cowt_set_from_pset_spec2 ps μ qs.


Definition cowt_s_set_from_pset
  (ps : gset P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) : gset P :=
  coreachable_from [μ] ps hcocnv.

Lemma cowt_s_set_from_pset_ispec
  (ps : gset P) μ (hcocnv : forall p, p ∈ ps -> p ⇓ᶜᵒ [μ]) :
  cowt_set_from_pset_spec ps μ (cowt_s_set_from_pset ps μ hcocnv).
Proof.
  split.
  - intros q (p & hp & w)%coreachable_from_spec. exists p. split; assumption.
  - intros p q hp w. apply coreachable_from_spec. exists p. split; assumption.
Qed.

End coFiniteImage_sets.