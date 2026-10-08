(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

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

(** * lqCCS: the process LTS on one alphabet

    Processes [(P, ρ)] (a program and its memory) and observers (programs
    without memory, [lqCCS_Observers.v]) share one alphabet [lact]:

    - the messages [LOut c v] (non-blocking: an output is a parallel
      component) and [LIn c v], dual of each other;
    - the operations on the memory, [LOp E q̃] and [LMeas M q̃ k], each its own
      dual: an observer's prefix [E(q̃)] meets the memory of the process,
      which applies [E] to [ρ], in one synchronisation; for [M(q̃ ▷ x)], the
      memory answers an outcome [k] of non-zero weight.  Both are blocking:
      the prefix blocks the observer, and the memory takes part in it.

    The process's own operations on its memory are silent.  This file: the
    alphabet, outputs as parallel components ([out_par]), the process LTS and
    its axioms (output-buffered agents with feedback, finite output chains),
    so that the forwarder construction [toFW] applies. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets gmap gmultiset.
From TestingTheory Require Import Lifted Paths States lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Succ lqCCS_Congruence lqCCS_LTS.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_Finite_Output_Chain Lts_FW.
From TestingTheory Require Import InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction.

(** ** The alphabet *)

Inductive lact : Type :=
| LOut (c : chan) (v : val)
| LIn (c : chan) (v : val)
| LOp (E : sop) (qs : list qubit)
| LMeas (M : meas) (qs : list qubit) (k : nat).

#[global] Instance lact_eq_dec : EqDecision lact.
Proof. solve_decision. Defined.

Notation lactsum := ((chan * val) + (chan * val) + (sop * list qubit)
                     + (meas * list qubit * nat))%type.

#[global] Instance lact_countable : Countable lact.
Proof.
  refine (inj_countable'
    (λ a : lact, match a with
       | LOut c v => inl (inl (inl (c, v)))
       | LIn c v => inl (inl (inr (c, v)))
       | LOp E qs => inl (inr (E, qs))
       | LMeas M qs k => inr (M, qs, k) end : lactsum)
    (λ s : lactsum, match s with
       | inl (inl (inl (c, v))) => LOut c v
       | inl (inl (inr (c, v))) => LIn c v
       | inl (inr (E, qs)) => LOp E qs
       | inr (M, qs, k) => LMeas M qs k end) _).
  by intros [].
Defined.

(** The co-action: messages are swapped, operations on the memory are their
    own co-actions. *)
Definition lco (a : lact) : lact :=
  match a with LOut c v => LIn c v | LIn c v => LOut c v | a => a end.

Lemma lco_involutive a : lco (lco a) = a.
Proof. by destruct a. Qed.

Definition is_out (a : lact) : Prop := match a with LOut _ _ => True | _ => False end.

#[global] Instance is_out_dec a : Decision (is_out a).
Proof. destruct a; simpl; apply _. Defined.

Lemma lco_sym : Symmetric (λ a b : lact, b = lco a).
Proof. intros a b ->. by rewrite lco_involutive. Qed.

Lemma lco_blocks β η : is_out η → η = lco β → ¬ is_out β.
Proof. intros Hη ->. destruct β; simpl in *; tauto. Qed.

#[global] Instance lact_ExtAction : ExtAction lact := {|
  non_blocking := is_out;
  non_blocking_dec := is_out_dec;
  dual a b := b = lco a;
  dual_dec a b := _ : Decision (b = lco a);
  dual_blocks β η Hη Hd := lco_blocks β η Hη Hd;
  duo_sym := lco_sym;
  exists_dual a := exist _ (lco a) eq_refl;
|}.

#[global] Instance lact_UniqueDual : UniqueDual lact.
Proof. unfold UniqueDual. intros η β Hd. exact Hd. Qed.

(** ** An output is a parallel component *)

Lemma cgr_par_comm P Q : PPar P Q ≡* PPar Q P.
Proof. apply cgr_of_cs, cs_par_comm. Qed.

Lemma cgr_par_assoc P Q R : PPar P (PPar Q R) ≡* PPar (PPar P Q) R.
Proof. apply cgr_of_cs, cs_par_assoc. Qed.

Lemma cgr_par_nil P : PPar P (PG (GNil [])) ≡* P.
Proof. apply cgr_of_cs, cs_par_nil. Qed.

Lemma out_par P t c v P' :
  pstep P (LAct t (AOut c v)) P' → P ≡* PPar P' (PSend t c (EVal v)).
Proof.
  intros Hs. remember (LAct t (AOut c v)) as l eqn:El. revert El.
  induction Hs; intros El; simplify_eq.
  - exfalso. by eapply gstep_not_out.
  - (* send *)
    etrans; [|symmetry; apply cgr_par_comm].
    etrans; [|symmetry; apply cgr_par_nil].
    apply cgr_of_cs, cs_send_val. by constructor.
  - etrans; [apply cgr_of_cs; by apply cs_ite_t|]. by apply IHHs.
  - etrans; [apply cgr_of_cs; by apply cs_ite_f|]. by apply IHHs.
  - (* parL *)
    etrans; [apply cgr_par_l; by apply IHHs|].
    etrans; [symmetry; apply cgr_par_assoc|].
    etrans; [apply cgr_par_r, cgr_par_comm|].
    apply cgr_par_assoc.
  - (* parR *)
    etrans; [apply cgr_par_r; by apply IHHs|]. apply cgr_par_assoc.
  - (* res *)
    rename c0 into d.
    assert (Hcd : c ≠ d) by (intros ->; apply H; do 2 eexists; by left).
    etrans; [apply cgr_res; by apply IHHs|].
    etrans; [apply cgr_res, cgr_par_comm|].
    etrans; [apply cgr_of_cs, cs_res_par; simpl; set_solver|].
    apply cgr_par_comm.
Qed.

(** ** Steps of a program in parallel with an output *)

Notation oproc t c v := (PSend t c (EVal v)).

Lemma ustep_out_par P c v P' :
  ustep P (UAct (AOut c v)) P' → ∃ t, P ≡* PPar P' (oproc t c v).
Proof.
  intros ([s|t a] & El & Hs); simpl in El; simplify_eq. exists t. by apply out_par.
Qed.

Lemma ustep_par_l P Q u P' : ustep P u P' → ustep (PPar P Q) u (PPar P' Q).
Proof. intros (l & <- & Hs). exists l. split; [done|]. by apply ps_parL. Qed.

Lemma ustep_par_out_emit Q t c v :
  ustep (PPar Q (oproc t c v)) (UAct (AOut c v)) (PPar Q (PG (GNil []))).
Proof. exists (LAct t (AOut c v)). split; [done|]. apply ps_parR. by constructor. Qed.

Lemma ustep_par_out_sync Q Q' t c v :
  ustep Q (UAct (AIn c v)) Q' → ustep (PPar Q (oproc t c v)) UTau (PPar Q' (PG (GNil []))).
Proof.
  intros ([s|t' a] & El & Hs); simpl in El; simplify_eq.
  exists (LTau (SPair t' t)). split; [done|]. eapply ps_syncR; [done|]. by constructor.
Qed.

(** What [Q ∥ c!v] can do: a step of [Q], the output, or [Q] receiving it. *)
Lemma ustep_par_out_inv Q t c v u X :
  ustep (PPar Q (oproc t c v)) u X →
    (∃ Q', ustep Q u Q' ∧ X = PPar Q' (oproc t c v))
  ∨ (u = UAct (AOut c v) ∧ X = PPar Q (PG (GNil [])))
  ∨ (u = UTau ∧ ∃ Q', ustep Q (UAct (AIn c v)) Q' ∧ X = PPar Q' (PG (GNil []))).
Proof.
  intros (l & <- & Hs).
  inversion Hs as [| | | |? ? ? Q' HQ|? ? ? O' HO|? ? t1 t2 c1 v1 Q' O' HQ HO|? ? t1 t2 c1 v1 Q' O' HQ HO|];
    subst.
  - left. exists Q'. split; [by exists l|done].
  - right; left. inversion HO; subst. simpl in *. simplify_eq. done.
  - inversion HO.
  - right; right. inversion HO; subst. simpl in *. simplify_eq.
    split; [done|]. exists Q'. split; [eexists; split; [|eassumption]; done|done].
Qed.

Lemma pstep_par_out_inv Q t c v t' a X :
  pstep (PPar Q (oproc t c v)) (LAct t' a) X → (∀ v', a ≠ AOut c v') →
  ∃ Q', pstep Q (LAct t' a) Q' ∧ X = PPar Q' (oproc t c v).
Proof.
  intros Hs Ha. inversion Hs as [| | | |? ? ? Q' HQ|? ? ? O' HO| | |]; subst.
  - eauto.
  - inversion HO; subst. by edestruct Ha.
Qed.

Lemma cgr_send_tag t t' c v : oproc t c v ≡* oproc t' c v.
Proof. apply cgr_of_cs, cs_send_val. by constructor. Qed.

(** Two emissions of the same message leave congruent programs. *)
Lemma out_det P t t' c v P1 P2 :
  pstep P (LAct t (AOut c v)) P1 → pstep P (LAct t' (AOut c v)) P2 → P1 ≡* P2.
Proof.
  intros Hs. remember (LAct t (AOut c v)) as l eqn:El. revert t' P2 El.
  induction Hs as [g l P' Hg|t0 c0 e v0 He|e P Q l P' He Hs IH|e P Q l Q' He Hs IH
                  |P Q l P' Hs IH|P Q l Q' Hs IH|P Q t1 t2 c1 v1 P' Q' Hs1 Hs2|P Q t1 t2 c1 v1 P' Q' Hs1 Hs2
                  |P d l P' Hd Hs IH];
    intros t' P2 El Hs'; simplify_eq.
  - exfalso. by eapply gstep_not_out.
  - inversion Hs'; subst. done.
  - inversion Hs'; subst; [by eapply IH|congruence].
  - inversion Hs'; subst; [congruence|by eapply IH].
  - inversion Hs' as [| | | |? ? ? P2' Hs2|? ? ? Q2 Hs2| | |]; subst.
    + apply cgr_par_l. by eapply IH.
    + (* P ∥ Q2 against P' ∥ Q *)
      apply out_par in Hs, Hs2.
      etrans; [apply cgr_par_r, Hs2|].
      etrans; [apply cgr_par_r, cgr_par_r, (cgr_send_tag t' t)|].
      etrans; [apply cgr_par_r, cgr_par_comm|].
      etrans; [apply cgr_par_assoc|].
      apply cgr_par_l. by symmetry.
  - inversion Hs' as [| | | |? ? ? P2' Hs2|? ? ? Q2 Hs2| | |]; subst.
    + apply out_par in Hs, Hs2.
      etrans; [apply cgr_par_l, Hs2|].
      etrans; [apply cgr_par_l, cgr_par_r, (cgr_send_tag t' t)|].
      etrans; [symmetry; apply cgr_par_assoc|].
      etrans; [apply cgr_par_r, cgr_par_comm|].
      apply cgr_par_r. by symmetry.
    + apply cgr_par_r. by eapply IH.
  - inversion Hs'; subst. apply cgr_res. by eapply IH.
Qed.

(** ** The messages a program can emit, with multiplicity *)

Fixpoint pouts (P : proc) : list (chan * val) :=
  match P with
  | PSend _ c e => match eval e with Some v => [(c, v)] | None => [] end
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => pouts P
      | Some (VBool false) => pouts Q
      | _ => []
      end
  | PPar P Q => pouts P ++ pouts Q
  | PRes P c => filter (λ cv, cv.1 ≠ c) (pouts P)
  | PG _ => []
  end.

Lemma pouts_step P t c v P' :
  pstep P (LAct t (AOut c v)) P' → pouts P ≡ₚ (c, v) :: pouts P'.
Proof.
  intros Hs. remember (LAct t (AOut c v)) as l eqn:El. revert El.
  induction Hs as [g l P' Hg|t0 c0 e v0 He|e P Q l P' He Hs IH|e P Q l Q' He Hs IH
                  |P Q l P' Hs IH|P Q l Q' Hs IH| | |P d l P' Hd Hs IH];
    intros El; simplify_eq; simpl.
  - exfalso. by eapply gstep_not_out.
  - by rewrite He.
  - rewrite He. by apply IH.
  - rewrite He. by apply IH.
  - by rewrite IH.
  - rewrite IH by done. by rewrite Permutation_middle.
  - assert (Hcd : c ≠ d) by (intros ->; apply Hd; do 2 eexists; by left).
    rewrite IH by done. rewrite filter_cons_True; [done|]. done.
Qed.

Lemma pouts_spec P c v : (c, v) ∈ pouts P → ∃ t P', pstep P (LAct t (AOut c v)) P'.
Proof.
  induction P as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP d|g]; simpl; intros Hin.
  - destruct (eval e) eqn:He; [|set_solver].
    apply list_elem_of_singleton in Hin. simplify_eq. eexists _, _. by constructor.
  - destruct (eval e) as [[[]| |]|] eqn:He; try set_solver.
    + destruct (IHP Hin) as (t & P' & Hs). eexists _, _. by apply ps_iteT.
    + destruct (IHQ Hin) as (t & P' & Hs). eexists _, _. by apply ps_iteF.
  - apply elem_of_app in Hin as [Hin|Hin].
    + destruct (IHP Hin) as (t & P' & Hs). eexists _, _. by apply ps_parL.
    + destruct (IHQ Hin) as (t & P' & Hs). eexists _, _. by apply ps_parR.
  - apply list_elem_of_filter in Hin as [Hcd Hin]. simpl in Hcd.
    destruct (IHP Hin) as (t & P' & Hs). eexists _, _. apply ps_res; [|done].
    intros (t' & v' & [El|El]); by simplify_eq.
  - set_solver.
Qed.

(** ** The process LTS: a program and its memory *)

Section Process.
  Context `{QM : QuantumModel}.

  Notation pconf := (proc * St)%type.

  Inductive lstep : pconf → Act lact → pconf → Prop :=
  | ls_tau P P' ρ :
      ustep P UTau P' → lstep (P, ρ) τ (P', ρ)
  | ls_op P P' ρ t E qs :
      pstep P (LAct t (AOp E qs)) P' → lstep (P, ρ) τ (P', sop_apply E qs ρ)
  | ls_meas P P0 ρ t M qs y (k : Out (meas_of M qs)) :
      pstep P (LAct t (AMeas M qs y)) P0 → nonzero (meas_branch M qs k ρ) →
      lstep (P, ρ) τ (subst P0 y (VNat (code _ k)), meas_branch M qs k ρ)
  | ls_out P P' ρ c v :
      ustep P (UAct (AOut c v)) P' → lstep (P, ρ) (ActExt (LOut c v)) (P', ρ)
  | ls_in P P' ρ c v :
      ustep P (UAct (AIn c v)) P' → lstep (P, ρ) (ActExt (LIn c v)) (P', ρ)
  | ls_mop P ρ E qs :
      lstep (P, ρ) (ActExt (LOp E qs)) (P, sop_apply E qs ρ)
  | ls_mmeas P ρ M qs (k : Out (meas_of M qs)) :
      nonzero (meas_branch M qs k ρ) →
      lstep (P, ρ) (ActExt (LMeas M qs (code _ k))) (P, meas_branch M qs k ρ).

  Definition meas_succs {C} (M : meas) (qs : list qubit) (ρ : St)
    (f : Out (meas_of M qs) → C) : list C :=
    f <$> filter (λ k, nonzero (meas_branch M qs k ρ)) (outs (meas_of M qs)).

  Definition meas_succs_at {C} (M : meas) (qs : list qubit) (n : nat) (ρ : St)
    (f : Out (meas_of M qs) → C) : list C :=
    f <$> filter (λ k, code _ k = n ∧ nonzero (meas_branch M qs k ρ)) (outs (meas_of M qs)).

  Definition lsuccs (x : pconf) (α : Act lact) : list pconf :=
    let '(P, ρ) := x in
    match α with
    | τ =>
        ((λ P', (P', ρ)) <$> succ P UTau)
        ++ (acts P ≫= λ '(a, P0),
              match a with
              | AOp E qs => [(P0, sop_apply E qs ρ)]
              | AMeas M qs y =>
                  meas_succs M qs ρ (λ k, (subst P0 y (VNat (code _ k)), meas_branch M qs k ρ))
              | _ => []
              end)
    | ActExt (LOut c v) => (λ P', (P', ρ)) <$> succ P (UAct (AOut c v))
    | ActExt (LIn c v) => (λ P', (P', ρ)) <$> succ P (UAct (AIn c v))
    | ActExt (LOp E qs) => [(P, sop_apply E qs ρ)]
    | ActExt (LMeas M qs n) => meas_succs_at M qs n ρ (λ k, (P, meas_branch M qs k ρ))
    end.

  Lemma meas_succs_spec {C} M qs ρ (f : Out (meas_of M qs) → C) y :
    y ∈ meas_succs M qs ρ f ↔ ∃ k, nonzero (meas_branch M qs k ρ) ∧ y = f k.
  Proof.
    unfold meas_succs. rewrite list_elem_of_fmap. split.
    - intros (k & -> & Hk). apply list_elem_of_filter in Hk as [Hn _]. eauto.
    - intros (k & Hn & ->). exists k. split; [done|].
      apply list_elem_of_filter. split; [done|]. apply list_elem_of_In, outs_all.
  Qed.

  Lemma meas_succs_at_spec {C} M qs n ρ (f : Out (meas_of M qs) → C) y :
    y ∈ meas_succs_at M qs n ρ f ↔ ∃ k, code _ k = n ∧ nonzero (meas_branch M qs k ρ) ∧ y = f k.
  Proof.
    unfold meas_succs_at. rewrite list_elem_of_fmap. split.
    - intros (k & -> & Hk). apply list_elem_of_filter in Hk as [[Hc Hn] _]. eauto.
    - intros (k & Hc & Hn & ->). exists k. split; [done|].
      apply list_elem_of_filter. split; [done|]. apply list_elem_of_In, outs_all.
  Qed.

  Lemma lsuccs_spec x α z : z ∈ lsuccs x α ↔ lstep x α z.
  Proof.
    destruct x as [P ρ]. split.
    - destruct α as [[c v|c v|E qs|M qs n]|]; simpl.
      + rewrite list_elem_of_fmap. intros (P' & -> & Hs). apply succ_spec in Hs. by constructor.
      + rewrite list_elem_of_fmap. intros (P' & -> & Hs). apply succ_spec in Hs. by constructor.
      + intros Hz. apply list_elem_of_singleton in Hz as ->. constructor.
      + intros Hz. apply meas_succs_at_spec in Hz as (k & <- & Hn & ->). by constructor.
      + rewrite elem_of_app, list_elem_of_fmap, list_elem_of_bind.
        intros [(P' & -> & Hs)|([a P0] & Hin & Hacts)].
        * apply succ_spec in Hs. by constructor.
        * apply acts_spec in Hacts as (_ & t & Hs).
          destruct a as [c v|c v|E qs|M qs y']; try set_solver.
          -- apply list_elem_of_singleton in Hin as ->. by econstructor.
          -- apply meas_succs_spec in Hin as (k & Hn & ->). by econstructor.
    - intros Hs. inversion Hs; subst; simpl.
      + apply elem_of_app. left. apply list_elem_of_fmap. eexists. split; [done|].
        by apply succ_spec.
      + apply elem_of_app. right. apply list_elem_of_bind. exists (AOp E qs, P').
        split; [set_solver|]. apply acts_spec. split; [done|]. eauto.
      + apply elem_of_app. right. apply list_elem_of_bind.
        match goal with Hp : pstep _ (LAct _ (AMeas ?M ?qs ?y)) ?P0 |- _ =>
          exists (AMeas M qs y, P0) end.
        split; [apply meas_succs_spec; eauto|]. apply acts_spec. split; [done|]. eauto.
      + apply list_elem_of_fmap. eexists. split; [done|]. by apply succ_spec.
      + apply list_elem_of_fmap. eexists. split; [done|]. by apply succ_spec.
      + set_solver.
      + apply meas_succs_at_spec. eauto.
  Qed.

  #[global] Instance pconf_gLts : gLts pconf lact_ExtAction := gLts_of_succs lsuccs.

  Lemma pconf_step_def x α y : x ⟶{α} y ↔ lstep x α y.
  Proof. change (y ∈ lsuccs x α ↔ lstep x α y). apply lsuccs_spec. Qed.

  (** ** Transfer of program steps along [≡*] *)

  Lemma cgr_ustep P Q u P1 : P ≡* Q → ustep P u P1 → ∃ Q1, ustep Q u Q1 ∧ P1 ≡* Q1.
  Proof.
    intros Hc (l & <- & Hs). destruct (cgr_bisim P Q Hc l P1 Hs) as (l' & Q1 & El & Hs' & HQ).
    exists Q1. split; [by exists l'|done].
  Qed.

  Lemma cgr_pstep_act P Q t a P1 : P ≡* Q → pstep P (LAct t a) P1 →
    ∃ t' Q1, pstep Q (LAct t' a) Q1 ∧ P1 ≡* Q1.
  Proof. intros Hc Hs. by eapply fwd_vis; [apply cgr_bisim|]. Qed.

  (** ** Equivalence of processes: congruent programs, same memory *)

  Definition feq (x y : pconf) : Prop := x.1 ≡* y.1 ∧ x.2 = y.2.

  #[global] Instance feq_equivalence : Equivalence feq.
  Proof.
    split.
    - intros x. split; done.
    - intros x y (Ha & Hb). split; by symmetry.
    - intros x y z (Ha & Hb) (Ha' & Hb'). split; [by etrans|congruence].
  Qed.

  Lemma feq_step x r α y : feq x r → lstep r α y → ∃ x', lstep x α x' ∧ feq x' y.
  Proof.
    destruct x as [P ρ]. intros (Hc & E2) Hs. simpl in *. symmetry in Hc.
    inversion Hs as [R R' ρ' Hu|R R' ρ' t E qs Hp|R R0 ρ' t M qs y' k Hp Hn
                    |R R' ρ' c v Hu|R R' ρ' c v Hu|R ρ' E qs|R ρ' M qs k Hn]; subst.
    - destruct (cgr_ustep _ _ _ _ Hc Hu) as (P'' & Hu' & HP).
      exists (P'', ρ'). split; [by constructor|]. split; simpl; by try symmetry.
    - destruct (cgr_pstep_act _ _ _ _ _ Hc Hp) as (t' & P'' & Hp' & HP).
      exists (P'', sop_apply E qs ρ'). split; [by econstructor|]. split; simpl; by try symmetry.
    - destruct (cgr_pstep_act _ _ _ _ _ Hc Hp) as (t' & P'' & Hp' & HP).
      exists (subst P'' y' (VNat (code _ k)), meas_branch M qs k ρ').
      split; [by econstructor|]. split; simpl; [|done].
      symmetry. by apply cgr_subst.
    - destruct (cgr_ustep _ _ _ _ Hc Hu) as (P'' & Hu' & HP).
      exists (P'', ρ'). split; [by constructor|]. split; simpl; by try symmetry.
    - destruct (cgr_ustep _ _ _ _ Hc Hu) as (P'' & Hu' & HP).
      exists (P'', ρ'). split; [by constructor|]. split; simpl; by try symmetry.
    - eexists. split; [constructor|]. split; simpl; by try symmetry.
    - eexists. split; [by constructor|]. split; simpl; by try symmetry.
  Qed.

  #[global] Instance pconf_gLtsEq : gLtsEq pconf lact_ExtAction.
  Proof.
    refine {| gLtsEq_gLts := pconf_gLts; eq_rel := feq; eq_rel_eq := _ |}.
    intros x y α (r & Hxr & Hr). apply pconf_step_def in Hr.
    destruct (feq_step x r α y Hxr Hr) as (x' & Hs & Hx').
    exists x'. split; [by apply pconf_step_def|done].
  Defined.

  (** ** A process in parallel with an output *)

  Definition fpar (x : pconf) t c v : pconf := (PPar x.1 (oproc t c v), x.2).

  Lemma lstep_par_out x α y t c v : lstep x α y → lstep (fpar x t c v) α (fpar y t c v).
  Proof.
    intros Hs. inversion Hs; subst; unfold fpar; simpl.
    - constructor. by apply ustep_par_l.
    - econstructor. by apply ps_parL.
    - match goal with |- lstep _ _ (PPar (subst ?P0 ?y ?n) ?O, _) =>
        change (PPar (subst P0 y n) O) with (subst (PPar P0 O) y n) end.
      econstructor; [by apply ps_parL|done].
    - constructor. by apply ustep_par_l.
    - constructor. by apply ustep_par_l.
    - constructor.
    - by constructor.
  Qed.

  Lemma lstep_par_out_inv x t c v α y :
    lstep (fpar x t c v) α y →
      (∃ y', lstep x α y' ∧ y = fpar y' t c v)
    ∨ (α = ActExt (LOut c v) ∧ y = (PPar x.1 𝟘, x.2))
    ∨ (α = τ ∧ ∃ P', ustep x.1 (UAct (AIn c v)) P' ∧ y = (PPar P' 𝟘, x.2)).
  Proof.
    destruct x as [P ρ]. unfold fpar; simpl. intros Hs.
    inversion Hs as [R R' ρ' Hu|R R' ρ' t' E qs Hp|R R0 ρ' t' M qs y' k Hp Hn
                    |R R' ρ' c' v' Hu|R R' ρ' c' v' Hu|R ρ' E qs|R ρ' M qs k Hn]; subst.
    - destruct (ustep_par_out_inv _ _ _ _ _ _ Hu)
        as [(Q' & HQ & ->)|[[E _]|[_ (Q' & HQ & ->)]]]; [|done|].
      + left. eexists (Q', _). split; [by constructor|done].
      + right; right. eauto.
    - destruct (pstep_par_out_inv _ _ _ _ _ _ _ Hp) as (Q' & HQ & ->); [done|].
      left. eexists (Q', _). split; [by econstructor|done].
    - destruct (pstep_par_out_inv _ _ _ _ _ _ _ Hp) as (Q' & HQ & ->); [done|].
      left. eexists (subst Q' y' (VNat (code _ k)), _). split; [by econstructor|done].
    - destruct (ustep_par_out_inv _ _ _ _ _ _ Hu)
        as [(Q' & HQ & ->)|[[E ->] |[E _]]]; [|simplify_eq|done].
      + left. eexists (Q', _). split; [by constructor|done].
      + right; left. done.
    - destruct (ustep_par_out_inv _ _ _ _ _ _ Hu)
        as [(Q' & HQ & ->)|[[E _]|[E _]]]; [|done|done].
      left. eexists (Q', _). split; [by constructor|done].
    - left. eexists (P, _). split; [constructor|done].
    - left. eexists (P, _). split; [by constructor|done].
  Qed.

  Lemma fout_cases x c v y : lstep x (ActExt (LOut c v)) y → ∃ t, feq x (fpar y t c v).
  Proof.
    intros Hs. inversion Hs as [| | |P P' ρ c' v' Hu| | |]; subst.
    destruct (ustep_out_par _ _ _ _ Hu) as [t Ht]. exists t. by split.
  Qed.

  Lemma feq_par_nil y : feq (PPar y.1 𝟘, y.2) y.
  Proof. split; simpl; [apply cgr_par_nil|done]. Qed.

  Lemma out_from_par x y t c v :
    feq x (fpar y t c v) → ∃ z, lstep x (ActExt (LOut c v)) z ∧ feq z y.
  Proof.
    intros Hx. destruct (feq_step x (fpar y t c v) (ActExt (LOut c v)) (PPar y.1 𝟘, y.2) Hx)
      as (z & Hz & Hzy).
    - constructor. apply ustep_par_out_emit.
    - exists z. split; [done|]. etrans; [exact Hzy|]. apply feq_par_nil.
  Qed.

  (** ** The output axioms *)

  Lemma f_nb_delay x y z c v α :
    lstep x (ActExt (LOut c v)) y → lstep y α z →
    ∃ w, lstep x α w ∧ ∃ z', lstep w (ActExt (LOut c v)) z' ∧ feq z' z.
  Proof.
    intros Hxy Hyz. destruct (fout_cases _ _ _ _ Hxy) as [t Hx].
    destruct (feq_step x _ _ _ Hx (lstep_par_out _ _ _ t c v Hyz)) as (w & Hw & Hwz).
    destruct (out_from_par _ _ _ _ _ Hwz) as (z' & Hz' & Hz'z). eauto.
  Qed.

  Lemma f_nb_confluence x y1 y2 c v μ :
    μ ≠ LOut c v → lstep x (ActExt (LOut c v)) y1 → lstep x (ActExt μ) y2 →
    ∃ r, lstep y1 (ActExt μ) r ∧ ∃ r', lstep y2 (ActExt (LOut c v)) r' ∧ feq r' r.
  Proof.
    intros Hμ Hs1 Hs2. destruct (fout_cases _ _ _ _ Hs1) as [t Hx].
    symmetry in Hx. destruct (feq_step _ _ _ _ Hx Hs2) as (z & Hz & Hzy).
    destruct (lstep_par_out_inv _ _ _ _ _ _ Hz)
      as [(y' & Hy' & ->)|[[E _]|[E _]]]; [|simplify_eq|done].
    exists y'. split; [done|]. symmetry in Hzy.
    destruct (out_from_par _ _ _ _ _ Hzy) as (r' & Hr' & Hr'y). eauto.
  Qed.

  Lemma f_nb_tau x y1 y2 c v :
    lstep x (ActExt (LOut c v)) y1 → lstep x τ y2 →
    (∃ t, lstep y1 τ t ∧ ∃ t', lstep y2 (ActExt (LOut c v)) t' ∧ feq t' t)
    ∨ (∃ t', lstep y1 (ActExt (LIn c v)) t' ∧ feq t' y2).
  Proof.
    intros Hs1 Hs2. destruct (fout_cases _ _ _ _ Hs1) as [t Hx].
    symmetry in Hx. destruct (feq_step _ _ _ _ Hx Hs2) as (z & Hz & Hzy).
    destruct (lstep_par_out_inv _ _ _ _ _ _ Hz)
      as [(y' & Hy' & ->)|[[E _]|[_ (P' & HP' & ->)]]]; [|done|].
    - left. exists y'. split; [done|]. symmetry in Hzy.
      destruct (out_from_par _ _ _ _ _ Hzy) as (r' & Hr' & Hr'y). eauto.
    - right. destruct y1 as [P1 ρ1]. exists (P', ρ1). split; [by constructor|].
      etrans; [symmetry; apply (feq_par_nil (P', ρ1))|exact Hzy].
  Qed.

  Lemma f_nb_determinacy x y1 y2 c v :
    lstep x (ActExt (LOut c v)) y1 → lstep x (ActExt (LOut c v)) y2 → feq y1 y2.
  Proof.
    intros Hs1 Hs2.
    inversion Hs1 as [| | |P P1 ρ c' v' Hu1| | |]; subst;
      inversion Hs2 as [| | |? P2 ? ? ? Hu2| | |]; subst.
    destruct Hu1 as ([s|t a] & E1 & Hp1); simpl in E1; simplify_eq.
    destruct Hu2 as ([s|t' a] & E2 & Hp2); simpl in E2; simplify_eq.
    split; simpl; [by eapply out_det|done].
  Qed.

  Lemma f_backwards_nb_determinacy x1 x2 y1 y2 c v :
    lstep x1 (ActExt (LOut c v)) y1 → lstep x2 (ActExt (LOut c v)) y2 → feq y1 y2 → feq x1 x2.
  Proof.
    intros Hs1 Hs2 Hy.
    destruct (fout_cases _ _ _ _ Hs1) as [t1 [Ht1 Hρ1]].
    destruct (fout_cases _ _ _ _ Hs2) as [t2 [Ht2 Hρ2]].
    destruct Hy as (Hc & Hρ). simpl in *. split; [|congruence].
    etrans; [exact Ht1|]. etrans; [|symmetry; exact Ht2].
    etrans; [apply cgr_par_l, Hc|]. apply cgr_par_r, cgr_send_tag.
  Qed.

  Lemma f_feedback x y z c v :
    lstep x (ActExt (LOut c v)) y → lstep y (ActExt (LIn c v)) z →
    ∃ w, lstep x τ w ∧ feq w z.
  Proof.
    intros Hs1 Hs2. destruct (fout_cases _ _ _ _ Hs1) as [t Hx].
    inversion Hs2 as [| | | |P P' ρ ? ? Hu| |]; subst.
    destruct (feq_step x (fpar (P, ρ) t c v) τ (PPar P' 𝟘, ρ) Hx) as (w & Hw & Hwz).
    - constructor. by apply ustep_par_out_sync.
    - exists w. split; [done|]. etrans; [exact Hwz|]. apply (feq_par_nil (P', ρ)).
  Qed.

  #[global] Instance pconf_gLtsOba : @gLtsOba pconf lact lact_ExtAction pconf_gLtsEq.
  Proof.
    split.
    - intros p q r η α Hη Hpq Hqr. destruct η as [c v| | |]; try done.
      apply pconf_step_def in Hpq, Hqr.
      destruct (f_nb_delay _ _ _ _ _ _ Hpq Hqr) as (w & Hw & z' & Hz' & Heq).
      exists w. split; [by apply pconf_step_def|].
      exists z'. split; [by apply pconf_step_def|exact Heq].
    - intros p q1 q2 η μ Hη Hμ Hs1 Hs2. destruct η as [c v| | |]; try done.
      apply pconf_step_def in Hs1, Hs2.
      destruct (f_nb_confluence _ _ _ _ _ _ Hμ Hs1 Hs2) as (r & Hr & r' & Hr' & Heq).
      exists r. split; [by apply pconf_step_def|].
      exists r'. split; [by apply pconf_step_def|exact Heq].
    - intros p q1 q2 η Hη Hs1 Hs2. destruct η as [c v| | |]; try done.
      apply pconf_step_def in Hs1, Hs2.
      destruct (f_nb_tau _ _ _ _ _ Hs1 Hs2) as [(t & Ht & t' & Ht' & Heq)|(t' & Ht' & Heq)].
      + left. exists t. split; [by apply pconf_step_def|].
        exists t'. split; [by apply pconf_step_def|exact Heq].
      + right. exists (LIn c v). split; [done|].
        exists t'. split; [by apply pconf_step_def|exact Heq].
    - intros p1 p2 p3 η Hη Hs1 Hs2. destruct η as [c v| | |]; try done.
      apply pconf_step_def in Hs1, Hs2. exact (f_nb_determinacy _ _ _ _ _ Hs1 Hs2).
    - intros p1 p2 q1 q2 η Hη Hs1 Hs2 Hq. destruct η as [c v| | |]; try done.
      apply pconf_step_def in Hs1, Hs2.
      exact (f_backwards_nb_determinacy _ _ _ _ _ _ Hs1 Hs2 Hq).
  Qed.

  #[global] Instance pconf_gLtsObaFB : gLtsObaFB pconf lact.
  Proof.
    split. intros p1 p2 p3 η β Hη Hd Hs1 Hs2. destruct η as [c v| | |]; try done.
    destruct β as [c' v'|c' v'| |]; simpl in Hd; simplify_eq.
    apply pconf_step_def in Hs1, Hs2.
    destruct (f_feedback _ _ _ _ _ Hs1 Hs2) as (w & Hw & Heq).
    exists w. split; [by apply pconf_step_def|exact Heq].
  Qed.

  (** ** The outputs a process can perform, with multiplicity *)

  Definition fmo (x : pconf) : gmultiset lact :=
    list_to_set_disj ((λ cv : chan * val, LOut cv.1 cv.2) <$> pouts x.1).

  Lemma fmo_elem x a : a ∈ fmo x ↔ ∃ c v, a = LOut c v ∧ (c, v) ∈ pouts x.1.
  Proof.
    unfold fmo. rewrite elem_of_list_to_set_disj, list_elem_of_fmap. split.
    - intros ([c v] & -> & Hin). eauto.
    - intros (c & v & -> & Hin). by exists (c, v).
  Qed.

  Lemma fmo_is_out x η : η ∈ fmo x → is_out η.
  Proof. intros (c & v & -> & _)%fmo_elem. done. Qed.

  Lemma fmo_step x η : η ∈ fmo x → ∃ y, lstep x (ActExt η) y.
  Proof.
    destruct x as [P ρ]. intros (c & v & -> & Hin)%fmo_elem.
    destruct (pouts_spec _ _ _ Hin) as (t & P' & Hs).
    eexists. constructor. exists (LAct t (AOut c v)). by split.
  Qed.

  Lemma fmo_spec1 x η y : is_out η → lstep x (ActExt η) y → η ∈ fmo x.
  Proof.
    intros Hη Hs. inversion Hs as [| | |P P' ρ c v Hu| | |]; subst; simpl in Hη; try done.
    apply fmo_elem. exists c, v. split; [done|].
    destruct Hu as ([s|t a] & E & Hs'); simpl in E; simplify_eq.
    simpl. rewrite (pouts_step _ _ _ _ _ Hs'). by left.
  Qed.

  Lemma fmo_spec2 x η y : is_out η → lstep x (ActExt η) y → fmo x = {[+ η +]} ⊎ fmo y.
  Proof.
    intros Hη Hs. inversion Hs as [| | |P P' ρ c v Hu| | |]; subst; simpl in Hη; try done.
    destruct Hu as ([s|t a] & E & Hs'); simpl in E; simplify_eq.
    unfold fmo. simpl. rewrite (pouts_step _ _ _ _ _ Hs'). done.
  Qed.

  Definition fmo_witness x η (Hin : η ∈ fmo x) : {y | is_out η ∧ x ⟶[η] y}.
  Proof.
    destruct (lsuccs x (ActExt η)) as [|y l] eqn:E.
    - exfalso. destruct (fmo_step x η Hin) as (y & Hy).
      apply lsuccs_spec in Hy. rewrite E in Hy. set_solver.
    - exists y. split; [by eapply fmo_is_out|].
      apply pconf_step_def, lsuccs_spec. rewrite E. by left.
  Defined.

  #[global] Instance pconf_FiniteOutputChain : FiniteOutputChain_LtsOba pconf (A := lact).
  Proof.
    refine {| lts_oba_mo := fmo; lts_oba_mo_spec_bis2 := fmo_witness |}.
    - intros p1 η p2 Hη Hs. apply pconf_step_def in Hs. by eapply fmo_spec1.
    - intros p η q Hη Hs. apply pconf_step_def in Hs. by eapply fmo_spec2.
  Defined.

  (** ** Interaction with the forwarder's mailbox *)

  #[global] Program Instance pconf_Inter_MO :
    Prop_of_Inter pconf (MO lact) lact lact fw_inter :=
    {| lts_essential_actions_left x := empty ;
       lts_essential_actions_right m := dom (MO_without_not_nb m) ;
       lts_co_inter_action_right m := fun x => empty |}.
  Next Obligation.
    intros ? ? hin; simpl in *. inversion hin.
  Qed.
  Next Obligation.
    intros m ξ hin; simpl in *.
    apply gmultiset_elem_of_dom in hin.
    assert (ξ ∈ MO_without_not_nb m) as hmem by eauto.
    apply lts_MO_nb_with_nb_spec1 in hmem as (nb & heq).
    apply gmultiset_disj_union_difference' in heq.
    exists (m ∖ {[+ ξ +]}). rewrite heq at 1.
    by apply lts_multiset_minus.
  Defined.
  Next Obligation.
    intros ? ? ? m ? m' ? ? hinter; simpl in *.
    right. destruct hinter as (duo & nb).
    eapply non_blocking_action_in_ms in nb as heq2; eauto.
    rewrite <- heq2.
    assert (MO_without_not_nb ({[+ μ2 +]} ⊎ m') = {[+ μ2 +]} ⊎ MO_without_not_nb m') as ->
      by (by apply lts_MO_nb_spec1).
    apply gmultiset_elem_of_dom. multiset_solver.
  Defined.
  Next Obligation.
    intros ξ x; simpl in *.
    destruct (decide (non_blocking ξ)) as [nb | not_nb].
    - exact {[ lco ξ ]}.
    - exact empty.
  Defined.
  Next Obligation.
    intros x x' ξ μ m hmem hl hinter; simpl in *.
    unfold pconf_Inter_MO_obligation_4.
    destruct hinter as (duo & nb). rewrite decide_True; [| eauto].
    simpl in duo. subst. rewrite lco_involutive. set_solver.
  Defined.
  Next Obligation.
    intros ? ? ? ? m hmem hl hinter; simpl in *. inversion hmem.
  Qed.

  (** The forwarder of [(P, ρ)]. *)
  Definition pconf_gLtsObaFW : gLtsObaFW (pconf * MO lact) lact := _.
End Process.
