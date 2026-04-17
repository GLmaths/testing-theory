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

From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap gmultiset.
From Must Require Import InListPropHelper ActTau gLts Bisimulation Termination WeakTransitions Convergence Lts_OBA_FB.

Class FiniteImagegLts P A `{gLts P A} :=
  MkFlts {
      folts_states_countable: Countable P;
      folts_next_states_finite p α : Finite (dsig (fun q => p ⟶{α} q));
}.

#[global] Existing Instance folts_states_countable.
#[global] Existing Instance folts_next_states_finite.

Class CountablegLts P A `{gLts P A} := MkClts {
    clts_states_countable: Countable P;
    clts_next_states_countable: ∀ x ℓ, Countable (dsig (fun y => x ⟶{ℓ} y));
}.
#[global] Existing Instance clts_states_countable.
#[global] Existing Instance clts_next_states_countable.


#[global] Instance finite_countable_lts `{FiniteImagegLts P A} : CountablegLts P A.
Proof. constructor; first apply _. intros *; apply finite_countable. Qed.

(******************************** Tools for Finite Image LTS ************************************)

(***************** Tau Set ***************************)
Definition lts_tau_set `{FiniteImagegLts P A} p : list P :=
  map proj1_sig (enum $ dsig (fun p' => p ⟶ p')).

Lemma lts_tau_set_spec : forall `{FiniteImagegLts P A} p q, q ∈ lts_tau_set p <-> p ⟶ q.
Proof.
  intros. split.
  intro mem. unfold lts_tau_set in mem.
  eapply elem_of_list_fmap in mem as ((r & l) & eq & mem). subst.
  eapply bool_decide_unpack. eassumption.
  intro. eapply elem_of_list_fmap.
  exists (dexist q H2). split.
  eauto. eapply elem_of_enum.
Qed.

Definition lts_tau_set_from_pset_spec1 `{Countable P, gLts P A}
  (ps : gset P) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟶ q.

Definition lts_tau_set_from_pset_spec2 `{Countable P, gLts P A}
  (ps : gset P) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟶ q -> q ∈ qs.

Definition lts_tau_set_from_pset_spec `{Countable P, gLts P A}
  (ps : gset P) (qs : gset P) :=
  lts_tau_set_from_pset_spec1 ps qs /\ lts_tau_set_from_pset_spec2 ps qs.

Definition lts_tau_set_from_pset `{FiniteImagegLts P A} (ps : gset P) : gset P :=
  ⋃ (map (fun p => list_to_set (lts_tau_set p)) (elements ps)).

Lemma lts_tau_set_from_pset_ispec `{gLts P A, !FiniteImagegLts P A}
  (ps : gset P) :
  lts_tau_set_from_pset_spec ps (lts_tau_set_from_pset ps).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (p & heq0 & mem1).
    subst.  eapply elem_of_list_to_set in mem2.
    eapply lts_tau_set_spec in mem2. multiset_solver.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (lts_tau_set p)).
    split.
    + multiset_solver.
    + eapply lts_tau_set_spec in l. multiset_solver.
Qed.

(***************** External Action Set ***************************)

Definition lts_extaction_set `{FiniteImagegLts P A} p μ : list P :=
  map proj1_sig (enum $ dsig (fun p' => p ⟶[ μ ] p')).

Lemma lts_extaction_set_spec : forall `{FiniteImagegLts P A} p μ q, 
        q ∈ lts_extaction_set p μ <-> p ⟶[ μ ] q.
Proof.
  intros. split.
  intro mem. unfold lts_tau_set in mem.
  eapply elem_of_list_fmap in mem as ((r & l) & eq & mem). subst.
  eapply bool_decide_unpack. eassumption.
  intro. eapply elem_of_list_fmap.
  exists (dexist q H2). split.
  eauto. eapply elem_of_enum.
Qed.

Definition lts_extaction_set_from_pset_spec1 `{Countable P, gLts P A}
  (ps : gset P) μ (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟶[ μ ] q.

Definition lts_extaction_set_from_pset_spec2 `{Countable P, gLts P A}
  (ps : gset P) μ (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟶[ μ ] q -> q ∈ qs.

Definition lts_extaction_set_from_pset_spec `{Countable P, gLts P A}
  (ps : gset P) μ (qs : gset P):=
  lts_extaction_set_from_pset_spec1 ps μ qs /\ lts_extaction_set_from_pset_spec2 ps μ qs.

Definition lts_extaction_set_from_pset `{FiniteImagegLts P A} (ps : gset P) μ : gset P :=
  ⋃ (map (fun p => list_to_set (lts_extaction_set p μ)) (elements ps)).

Lemma lts_extaction_set_from_pset_ispec `{gLts P A, !FiniteImagegLts P A}
  (ps : gset P) μ :
  lts_extaction_set_from_pset_spec ps μ (lts_extaction_set_from_pset ps μ).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (p & heq0 & mem1).
    subst.  eapply elem_of_list_to_set in mem2.
    eapply lts_extaction_set_spec in mem2. multiset_solver.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (lts_extaction_set p μ)).
    split.
    + multiset_solver.
    + eapply lts_extaction_set_spec in l. multiset_solver.
Qed.

(******** Weak Traces Sets **********)
Fixpoint wt_set_nil `{FiniteImagegLts P A} (p : P) (t : terminate p) : gset P :=
  let '(tstep _ f) := t in
  let k q := wt_set_nil (`q) (f (`q) (proj2_dsig q)) in
  {[ p ]} ∪ ⋃ map k (enum $ dsig (fun x => p ⟶ x)).

Lemma wt_set_nil_spec1 `{FiniteImagegLts P A} p q (tp : terminate p) :
  q ∈ wt_set_nil p tp -> p ⟹ q.
Proof.
  case tp. induction tp.
  intros t mem. simpl in mem.
  eapply elem_of_union in mem as [here | there].
  + eapply elem_of_singleton_1 in here. subst. eauto with mdb.
  + eapply elem_of_union_list in there as (ps & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (r & mem1 & eq). subst.
    eapply wt_tau; [|destruct (t (`r) (proj2_dsig r)) eqn:eqn0].
    ++ eapply (proj2_dsig r).
    ++ eapply H3. eapply (proj2_dsig r). eassumption.
Qed.

Lemma wt_set_nil_spec2 `{FiniteImagegLts P A} p q : 
    forall (tp : terminate p), p ⟹ q -> q ∈ wt_set_nil p tp.
Proof.
  intros. revert tp. dependent induction H2; intros tp; destruct tp.
  + set_solver.
  + eapply elem_of_union. right.
    eapply elem_of_union_list.
    set (qr := dexist q l).
    exists (wt_set_nil (`qr) (t0 (`qr) (proj2_dsig qr))).
    split. eapply elem_of_list_fmap.
    exists qr. split. reflexivity.
    eapply elem_of_enum. simpl.
    eapply IHwt. eauto.
Qed.

Lemma wt_nil_set_dec `{FiniteImagegLts P A} p (ht : p ⤓) : forall q, Decision (p ⟹ q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set_nil p ht)).
  - left. eapply (wt_set_nil_spec1 _ _ _ e).
  - right. intro wt. eapply n. now eapply wt_set_nil_spec2.
Qed.

Lemma wt_set_nil_fin_aux `{FiniteImagegLts P A}
  (p : P) (ht : terminate p) (d : ∀ q, Decision (p ⟹ q)) : 
      Finite (dsig (fun q => p ⟹ q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set_nil p ht))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_nil_spec2.
Qed.

Definition wt_set_nil_fin `{FiniteImagegLts P A}
  (p : P) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ q)) :=
  wt_set_nil_fin_aux p ht (wt_nil_set_dec p ht).

Lemma wt_push_nil_left_lts `{gLts P A} {p q r μ} : p ⟹ q -> q ⟶[μ] r -> p ⟹{μ} r.
Proof. by intros w1 lts; dependent induction w1; eauto with mdb. Qed.

Definition wt_set_mu
  `{FiniteImagegLts P A} (p : P)
  (μ : A) (s : trace A) (hcnv : p ⇓ μ :: s) : gset P :=
  let ht := cnv_terminate p (μ :: s) hcnv in
  let ps0 := @enum (dsig (fun q => p ⟹ q)) _ (wt_set_nil_fin p ht) in
  let f p : list (dsig (fun x => p ⟶[μ] x)) := enum (dsig (fun x => p ⟶[μ] x)) in
  ⋃ map (fun t =>
           ⋃ map (fun r =>
                    let w := wt_push_nil_left_lts (proj2_dsig t) (proj2_dsig r) in
                    let hcnv := cnv_preserved_by_wt_act s p μ hcnv (`r) w in
                    let htr := cnv_terminate (`r) s hcnv in
                    let ts := @enum (dsig (fun q => (`r) ⟹ q)) _ (wt_set_nil_fin (`r) htr) in
                    list_to_set (map (fun t => (`t)) ts)
             ) (f (`t))
    ) ps0.

Lemma wt_set_mu_spec1 `{FiniteImagegLts P A}
  (p q : P) (μ : A) (s : trace A) (hcnv : p ⇓ μ :: s) :
  q ∈ wt_set_mu p μ s hcnv -> p ⟹{μ} q.
Proof.
  intros mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  eapply elem_of_union_list in mem2 as (g & mem3 & mem4).
  eapply elem_of_list_fmap in mem3 as ((u & hlts) & eq & mem3). subst.
  eapply elem_of_list_to_set, elem_of_list_fmap in mem4 as ((v & hw2) & eq & mem4). subst.
  eapply wt_push_nil_left. eapply bool_decide_unpack. eassumption.
  eapply wt_act. eapply bool_decide_unpack. eassumption.
  eapply bool_decide_unpack. eassumption.
Qed.

Lemma wt_set_mu_spec2 `{FiniteImagegLts P A}
  (p q : P) (μ : A) (s : trace A) (hcnv : p ⇓ μ :: s) :
  p ⟹{μ} q -> q ∈ wt_set_mu p μ s hcnv.
Proof.
  intros w.
  eapply wt_decomp_one in w as (p0 & p1 & hw1 & hlts & hw2).
  eapply elem_of_union_list. eexists. split.
  eapply elem_of_list_fmap. exists (dexist p0 hw1). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_union_list. eexists. split.
  eapply elem_of_list_fmap. exists (dexist p1 hlts). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_list_to_set, elem_of_list_fmap.
  exists (dexist q hw2). split. reflexivity. eapply elem_of_enum.
Qed.

Lemma wt_mu_set_dec `{FiniteImagegLts P A} p μ s (hcnv : p ⇓ μ :: s) : 
    forall q, Decision (p ⟹{μ} q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set_mu p μ s hcnv)).
  - left. eapply  (wt_set_mu_spec1 p q μ s hcnv e).
  - right. intro wt. eapply n. now eapply wt_set_mu_spec2.
Qed.

Lemma wt_mu_set_fin_aux `{FiniteImagegLts P A}
  (p : P) μ s (hcnv : p ⇓ μ :: s) (d : ∀ q, Decision (p ⟹{μ} q)) : 
    Finite (dsig (fun q => p ⟹{μ} q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set_mu p μ s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_mu_spec2.
Qed.

Definition wt_set_mu_fin `{FiniteImagegLts P A}
  (p : P) μ s (hcnv : p ⇓ μ :: s) : Finite (dsig (fun q => p ⟹{μ} q)) :=
  wt_mu_set_fin_aux p μ s hcnv (wt_mu_set_dec p μ s hcnv).

Fixpoint wt_set `{FiniteImagegLts P A} (p : P) (s : trace A) (hcnv : cnv p s) : gset P :=
  match s as s0 return cnv p s0 -> gset P with
  | [] =>
      fun _ => wt_set_nil p (cnv_terminate p _ hcnv)
  | μ :: s' =>
      fun f =>
        let ts := @enum (dsig (fun q => p ⟹{μ} q)) _ (wt_set_mu_fin p μ s' f) in
        ⋃ map (fun t =>
                 let hcnv := cnv_preserved_by_wt_act s' p μ f (`t) (proj2_dsig t) in
                 wt_set (`t) s' hcnv
          ) ts
  end hcnv.

Lemma wt_set_spec1 `{FiniteImagegLts P A}
  (p q : P) (s : trace A) (hcnv : p ⇓ s) :
  q ∈ wt_set p s hcnv -> p ⟹[s] q.
Proof.
  revert p q hcnv. induction s; intros p q hcnv mem; simpl in *.
  - eapply wt_set_nil_spec1. eassumption.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    eapply wt_push_left. eapply bool_decide_unpack. eassumption.
    eapply IHs. eassumption.
Defined.

Lemma wt_set_spec2 `{FiniteImagegLts P A}
  (p q : P) (s : trace A) (hcnv : p ⇓ s) :
  p ⟹[s] q -> q ∈ wt_set p s hcnv.
Proof.
  revert p q hcnv.
  induction s as [|μ s']; intros p q hcnv w; simpl in *.
  - eapply wt_set_nil_spec2. eauto with mdb.
  - eapply wt_pop in w as (t & w1 & w2).
    eapply elem_of_union_list.
    eexists. split.
    + eapply elem_of_list_fmap.
      exists (dexist t w1). now split; [|eapply elem_of_enum].
    + now eapply IHs'.
Defined.

Lemma wt_set_dec `{FiniteImagegLts P A} p s (hcnv : p ⇓ s) : 
    forall q, Decision (p ⟹[s] q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set p s hcnv)).
  - left. eapply  (wt_set_spec1 p q s hcnv e).
  - right. intro wt. eapply n. now eapply wt_set_spec2.
Qed.

Lemma wt_set_fin_aux `{FiniteImagegLts P A}
  (p : P) s (hcnv : p ⇓ s) (d : ∀ q, Decision (p ⟹[s] q)) : 
    Finite (dsig (fun q => p ⟹[s] q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set p s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_spec2.
Qed.

Definition wt_set_fin `{FiniteImagegLts P A}
  (p : P) s (hcnv : p ⇓ s) : Finite (dsig (fun q => p ⟹[s] q)) :=
  wt_set_fin_aux p s hcnv (wt_set_dec p s hcnv).

Fixpoint wt_nil_refuses_set `{FiniteImagegLts P A} (p : P) (ht : p ⤓) : gset P :=
  match lts_refuses_decidable p τ with
  | left  _ => {[ p ]}
  | right _ =>
      let '(tstep _ f) := ht in
      let k p := wt_nil_refuses_set (`p) (f (`p) (proj2_dsig p)) in
      ⋃ map k (enum (dsig (fun q => p ⟶ q)))
  end.

Lemma wt_nil_refuses_set_spec1 `{FiniteImagegLts P A}
  (p q : P) (ht : p ⤓) :
  q ∈ wt_nil_refuses_set p ht -> p ⟹ q /\ q ↛.
Proof.
  case ht. induction ht.
  intros ht mem.
  simpl in mem.
  case (lts_refuses_decidable p τ) in mem.
  - eapply elem_of_singleton_1 in mem. subst. eauto with mdb.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    simpl in mem2. case (ht t (proj2_dsig (t ↾ hw1))) eqn:eq.
    edestruct (H3 t). now eapply bool_decide_unpack. eassumption.
    split; eauto with mdb. eapply wt_tau. eapply bool_decide_unpack.
    eassumption. eassumption.
Qed.

Lemma wt_nil_refuses_set_spec2 `{FiniteImagegLts P A}
  (p q : P) (ht : p ⤓) :
  (p ⟹ q /\ q ↛) -> q ∈ wt_nil_refuses_set p ht.
Proof.
  intros (hw & hst). dependent induction hw; case ht; induction ht; intros ht; simpl.
  - case (lts_refuses_decidable p τ); set_solver.
  - case (lts_refuses_decidable p τ); intro hst'.
    + exfalso. eapply (lts_refuses_spec2 p τ); eauto.
    + eapply elem_of_union_list.
      eexists. split. eapply elem_of_list_fmap.
      exists (dexist q l). split. reflexivity. eapply elem_of_enum. eapply IHhw; eauto.
Qed.

Lemma wt_nil_refuses_set_dec `{FiniteImagegLts P A} p (ht : p ⤓) : 
  forall q, Decision (p ⟹ q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ wt_nil_refuses_set p ht)).
  - left. eapply (wt_nil_refuses_set_spec1 p q ht e).
  - right. intro wt. eapply n. now eapply wt_nil_refuses_set_spec2.
Qed.

Lemma wt_nil_refuses_set_fin_aux `{FiniteImagegLts P A}
  (p : P) (ht : p ⤓) (d : ∀ q, Decision (p ⟹ q /\ q ↛)) : 
    Finite (dsig (fun q => p ⟹ q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_nil_refuses_set p ht))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_nil_refuses_set_spec2.
Qed.

Definition wt_nil_refuses_set_fin `{FiniteImagegLts P A}
  (p : P) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ q /\ q ↛)) :=
  wt_nil_refuses_set_fin_aux p ht (wt_nil_refuses_set_dec p ht).

Lemma cnv_wt_s_terminate `{gLts P A}
  (p q : P) s (hcnv : p ⇓ s) : p ⟹[s] q -> q ⤓.
Proof. eapply cnv_iff_prefix_terminate; eauto. Qed.

Definition wt_refuses_set `{FiniteImagegLts P A} (p : P) s (hcnv : p ⇓ s) : gset P :=
  let ps := @enum (dsig (fun q => p ⟹[s] q)) _ (wt_set_fin p s hcnv) in
  let k t := wt_nil_refuses_set (`t) (cnv_wt_s_terminate p (`t) s hcnv (proj2_dsig t)) in
  ⋃ map k ps.

Lemma wt_refuses_set_spec1 `{FiniteImagegLts P A}
  (p q : P) s (hcnv : p ⇓ s) :
  q ∈ wt_refuses_set p s hcnv -> p ⟹[s] q /\ q ↛.
Proof.
  intro mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  simpl in mem2.
  eapply wt_nil_refuses_set_spec1 in mem2.
  split. eapply wt_push_nil_right. eapply bool_decide_unpack. eassumption. firstorder.
  firstorder.
Qed.

Lemma wt_refuses_set_spec2 `{FiniteImagegLts P A}
  (p q : P) s (hcnv : p ⇓ s) :
  (p ⟹[s] q /\ q ↛) -> q ∈ wt_refuses_set p s hcnv.
Proof.
  intros (hw & hst).
  eapply elem_of_union_list.
  eexists. split. eapply elem_of_list_fmap.
  exists (dexist q hw). split. reflexivity. eapply elem_of_enum.
  simpl. eapply wt_nil_refuses_set_spec2. eauto with mdb.
Qed.

Lemma wt_refuses_set_fin_aux `{FiniteImagegLts P A}
  (p : P) s (hcnv : p ⇓ s) (d : ∀ q, Decision (p ⟹[s] q /\ q ↛)) : 
  Finite (dsig (fun q => p ⟹[s] q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_refuses_set p s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_refuses_set_spec2.
Qed.


Lemma wt_refuses_set_dec `{FiniteImagegLts P A} p s (hcnv : p ⇓ s) : 
  forall q, Decision (p ⟹[s] q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ wt_refuses_set p s hcnv)).
  - left. eapply (wt_refuses_set_spec1 p q s hcnv e).
  - right. intro wt. eapply n. now eapply wt_refuses_set_spec2.
Qed.

Definition wt_refuses_set_fin `{FiniteImagegLts P A}
  (p : P) s (hcnv : p ⇓ s) : Finite (dsig (fun q => p ⟹[s] q /\ q ↛)) :=
  wt_refuses_set_fin_aux p s hcnv (wt_refuses_set_dec p s hcnv).

Lemma wt_nil_set_refuses `{FiniteImagegLts P A} p hcnv :
  lts_refuses p τ -> wt_set p [] hcnv = {[ p ]}.
Proof.
  intros hst.
  eapply leibniz_equiv.
  intro q. split.
  - intro mem.
    eapply wt_set_spec1 in mem.
    inversion mem; subst.
    + set_solver.
    + exfalso. eapply lts_refuses_spec2; eauto.
  - intro mem. eapply wt_set_spec2. replace q with p.
    eauto with mdb. set_solver.
Qed.

Lemma wt_refuses_set_refuses_singleton `{FiniteImagegLts P A} p hcnv :
  lts_refuses p τ -> wt_refuses_set p [] hcnv = {[ p ]}.
Proof.
  intro hst.
  eapply leibniz_equiv.
  intro q. split; intro mem.
  - eapply wt_refuses_set_spec1 in mem as (w & hst').
    inversion w; subst. set_solver. exfalso. eapply lts_refuses_spec2; eauto.
  - eapply elem_of_singleton_1 in mem. subst.
    eapply wt_refuses_set_spec2. split; eauto with mdb.
Qed.

Fixpoint wt_s_set_from_pset_xs `{gLts P A, !FiniteImagegLts P A}
  (ps : list P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) : gset P :=
  match ps as ps0 return (forall p, p ∈ ps0 -> p ⇓ s) -> gset P with
  | [] => fun _ => ∅
  | p :: ps' =>
      fun ha =>
        let pr := ha p (elem_of_list_here p ps') in
        let ys := wt_set p s pr in
        let ha' := fun q mem => ha q (elem_of_list_further q p ps' mem) in
        ys ∪ wt_s_set_from_pset_xs ps' s ha'
  end hcnv.

Definition wt_set_from_pset_spec1_xs `{FiniteImagegLts P A}
  (ps : list P) (s : trace A) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹[s] q.

Definition wt_set_from_pset_spec2_xs `{FiniteImagegLts P A}
  (ps : list P) (s : trace A) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟹[s] q -> q ∈ qs.

Definition wt_set_from_pset_spec_xs `{FiniteImagegLts P A}
  (ps : list P) (s : trace A) (qs : gset P) :=
  wt_set_from_pset_spec1_xs ps s qs /\ wt_set_from_pset_spec2_xs ps s qs.

Lemma wt_s_set_from_pset_xs_ispec `{gLts P A, !FiniteImagegLts P A}
  (ps : list P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  wt_set_from_pset_spec_xs ps s (wt_s_set_from_pset_xs ps s hcnv).
Proof.
  split.
  - induction ps as [|p ps].
    intros p mem. set_solver.
    intros p' mem. simpl in *.
    eapply elem_of_union in mem as [hl|hr].
    exists p. split.
    set_solver. now eapply wt_set_spec1 in hl.
    eapply IHps in hr as (p0 & mem & hwp0).
    exists p0. repeat split; set_solver.
  - induction ps as [|p ps].
    + intros p'. set_solver.
    + intros p' q mem hwp'.
      eapply elem_of_union.
      inversion mem; subst.
      ++ left. eapply wt_set_spec2; eauto.
      ++ right. eapply IHps in hwp'; eauto.
Qed.

Lemma lift_cnv_elements `{gLts P A, !FiniteImagegLts P A}
  (ps : gset P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  forall p, p ∈ (elements ps) -> p ⇓ s.
Proof.
  intros p mem.
  eapply hcnv. now eapply elem_of_elements.
Qed.

Definition wt_s_set_from_pset `{gLts P A, !FiniteImagegLts P A}
  (ps : gset P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) : gset P :=
  wt_s_set_from_pset_xs (elements ps) s (lift_cnv_elements ps s hcnv).

Definition wt_set_from_pset_spec1 `{Countable P, gLts P A}
  (ps : gset P) (s : trace A) (qs : gset P) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹[s] q.

Definition wt_set_from_pset_spec2 `{FiniteImagegLts P A}
  (ps : gset P) (s : trace A) (qs : gset P) :=
  forall p q, p ∈ ps -> p ⟹[s] q -> q ∈ qs.

Definition wt_set_from_pset_spec `{FiniteImagegLts P A}
  (ps : gset P) (s : trace A) (qs : gset P) :=
  wt_set_from_pset_spec1 ps s qs /\ wt_set_from_pset_spec2 ps s qs.

Lemma wt_s_set_from_pset_ispec `{gLts P A, !FiniteImagegLts P A}
  (ps : gset P) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  wt_set_from_pset_spec ps s (wt_s_set_from_pset ps s hcnv).
Proof.
  split.
  - intros p mem.
    eapply wt_s_set_from_pset_xs_ispec in mem as (p' & mem & hwp').
    exists p'. split; set_solver.
  - intros p q mem hwp.
    eapply wt_s_set_from_pset_xs_ispec.
    eapply elem_of_elements; eassumption. eassumption.
Qed.

Definition eq_rel_set `{FiniteImagegLts P A} `{!gLtsEq P A} (X Y : gset P) :=
 (forall x, x ∈ X -> exists y, y ∈ Y ∧ eq_rel x y) ∧
 (forall y, y ∈ Y -> exists x, x ∈ X ∧ eq_rel y x).

Global Instance symmetric_eq_rel_set `{FiniteImagegLts P A} `{!gLtsEq P A}:
 Symmetric eq_rel_set.
Proof. intros x y. unfold eq_rel_set. intuition. Qed.

Global Instance reflexive_eq_rel_set `{FiniteImagegLts P A} `{!gLtsEq P A}:
 Reflexive eq_rel_set.
Proof. intro X; split; intros x Hx; exists x; intuition. reflexivity. reflexivity. Qed.

Global Instance equiv_eq_rel_set `{FiniteImagegLts P A} `{!gLtsEq P A}:
 Proper ((≡) ==> (≡) ==> (impl)) eq_rel_set.
Proof.
intros X X' HX Y Y' HY Heq. split; intros x Hx.
- apply HX, Heq in Hx as (y & Hy & Heq'). apply HY in Hy. eauto.
- apply HY, Heq in Hx as (y & Hy & Heq'). apply HX in Hy. eauto.
Qed.

Global Instance proper_singleton_elem_eq_rel_set
  `{FiniteImagegLts P A} `{!gLtsEq P A}:
  Proper ((eq_rel) ==> (eq_rel_set)) singleton.
Proof.
  intros x y Hx. split; intros x' Hx'%elem_of_singleton;
  subst x'; [exists y|exists x]; split; eauto; try apply elem_of_singleton; trivial.
  now symmetry.
Qed.

Global Instance eq_rel_set_union `{FiniteImagegLts P A} `{!gLtsEq P A}:
  Proper ((eq_rel_set) ==> (eq_rel_set) ==> (eq_rel_set)) union.
Proof.
intros X X' HX Y Y' HY.
split; setoid_rewrite elem_of_union; intros x [Hx|Hx];
 (apply HX in Hx || apply HY in Hx); destruct Hx as (y & Hy & Heq); eauto.
Qed.

Lemma wt_set_from_pset_spec_eq_rel_set `{FiniteImagegLts P A} `{!gLtsEq P A}:
  forall {X X' s Y}, eq_rel_set X X' -> (∀ p : P, p ∈ X → p ⇓ s) ->
  wt_set_from_pset_spec X s Y
  -> exists Y', eq_rel_set Y Y' ∧ wt_set_from_pset_spec X' s Y'.
Proof.
  intros X X' s Y HXX' Hcnv Hwt.
  assert (hcnv' : ∀ p : P, p ∈ X' → p ⇓ s).
  { intros p Hp. apply HXX' in Hp as (p' & Hp' & Heqp').
    rewrite Heqp'. now apply Hcnv. }
  unshelve eexists (wt_s_set_from_pset X' s hcnv').
  assert(Hps' := wt_s_set_from_pset_ispec X' s hcnv').
  split; trivial. split.
  - intros x Hx. apply Hwt in Hx as (p & Hin & Hp).
    apply HXX' in Hin as (x' & Hx' & Heq').
    eapply eq_spec_wt in Hp as (y & Hy & Heq''); [|exact Heq'].
    exists y; split; trivial. eapply Hps'; eauto. now symmetry.
  - intros x Hx. apply Hps' in Hx as (p & Hin & Hp).
    apply HXX' in Hin as (x' & Hx' & Heq').
    eapply eq_spec_wt in Hp as (y & Hy & Heq''); [|exact Heq'].
    exists y; split; trivial. eapply Hwt; eauto. now symmetry.
Qed.

Lemma wt_set_union `{FiniteImagegLts P A} (X1 X2 : gset P) (s : trace A) {ps}
  (Hcnv : ∀ p : P, p ∈ X1 ∪ X2 → p ⇓ s)
  : wt_set_from_pset_spec (X1 ∪ X2) s ps
    -> exists ps1 ps2, wt_set_from_pset_spec X1 s ps1
                 /\ wt_set_from_pset_spec X2 s ps2
                 /\ (ps = ps1 ∪ ps2) .
Proof.
  intros [Hw1 Hw2].
  assert(Hcnv1 : ∀ p : P, p ∈ X1 → p ⇓ s) by (intros; apply Hcnv; set_solver).
  assert(Hcnv2 : ∀ p : P, p ∈ X2 → p ⇓ s) by (intros; apply Hcnv; set_solver).
  exists (wt_s_set_from_pset X1 s Hcnv1).
  exists (wt_s_set_from_pset X2 s Hcnv2).
  do 2 (split; [apply wt_s_set_from_pset_ispec|]).
  apply leibniz_equiv.
  apply set_equiv. intro x; split; intro Hin.
  - destruct (Hw1 _ Hin) as (p & Hinp%elem_of_union & Hp).
    destruct Hinp as [Hin1 | Hin2].
    + eapply elem_of_union_l, wt_s_set_from_pset_ispec; eauto.
    + eapply elem_of_union_r, wt_s_set_from_pset_ispec; eauto.
  - rewrite elem_of_union in Hin.
    destruct Hin as [Hin | Hin];
    apply wt_s_set_from_pset_ispec in Hin as (p & Hin & Hp);
    eapply Hw2; eauto; set_solver.
Qed.

(* faster than set set_solver *)
Ltac set_tac :=
solve[apply elem_of_union_r; set_tac] ||
solve[apply elem_of_union_l; set_tac] ||
assumption ||
now apply elem_of_singleton_2.

Global Instance Proper_eq_rel_set_l `{FiniteImagegLts P A} `{!gLtsEq P A}:
  Proper ((eq_rel) ==> (=) ==> (eq_rel_set)) (fun p X => {[p]} ∪ X).
Proof.
intros p p' HX ???; subst. apply eq_rel_set_union; trivial.
split; setoid_rewrite elem_of_singleton;
intros x Hx; subst; eexists; split; trivial. now symmetry. reflexivity.
Qed.

Global Instance Proper_wt_set_from_pset_spec `{gLts P A, !FiniteImagegLts P A} :
    Proper ((≡) ==> (=) ==> (≡) ==> (iff)) wt_set_from_pset_spec.
  Proof.
    intros ps1 ps2 Hps s s' Hs ps1' ps2' Hps'.
    unfold wt_set_from_pset_spec, wt_set_from_pset_spec1, wt_set_from_pset_spec2.
    subst. setoid_rewrite Hps. setoid_rewrite Hps'. trivial.
  Qed.

Lemma wt_set_from_pset_spec_unique `{FiniteImagegLts P A} `{!gLtsEq P A} ps s ps' ps'' :
    wt_set_from_pset_spec ps s ps' ->
    wt_set_from_pset_spec ps s ps'' -> ps' ≡ ps''.
  Proof.
    intros [H1' H2'] [H1'' H2'']. apply set_equiv. intro x; split; intro Hin.
    - destruct (H1' _ Hin) as (p & Hinp & Hp). eapply H2''; eauto.
    - destruct (H1'' _ Hin) as (p & Hinp & Hp). eapply H2'; eauto.
  Qed.

(* Lemma wt_set_from_pset_spec_is_wt_s_set_from_pset `{FiniteImagegLts P A} `{!gLtsEq P A}
(ps : gset A) s ps' (hcnv : forall p, p ∈ ps -> p ⇓ s) :
wt_set_from_pset_spec ps s ps' -> ps' ≡ wt_s_set_from_pset ps s hcnv.
Proof.
  intro Hps'.
  eapply wt_set_from_pset_spec_unique; eauto using wt_s_set_from_pset_ispec.
Qed. *)