(* begin hide *)
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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
From Stdlib.Bool Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull.

#[local] Open Scope lqccs_scope.

Inductive tite (W : proc) : proc → Prop :=
| ti_refl : tite W W
| ti_T e Y A : eval e = Some (VBool true) → tite W Y → tite W (PIte e Y A)
| ti_F e Y A : eval e = Some (VBool false) → tite W Y → tite W (PIte e A Y).

Fixpoint gheads (g : guard) : list (prefix * proc) :=
  match g with
  | GNil _ | ① => []
  | 𝜆 ∙ P => [(𝜆, P)]
  | g1 ⊕ g2 => gheads g1 ++ gheads g2
  end.

Definition sh (𝜆 : prefix) (Q : proc) : proc := Nat.iter (prefix_binds 𝜆) (shiftv 0) Q.

Fixpoint heads (Z : proc) : list (prefix * proc) :=
  match Z with
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => heads P
      | Some (VBool false) => heads Q
      | _ => []
      end
  | P ∥ Q => map (λ h, (h.1, h.2 ∥ sh h.1 Q)) (heads P) ++ map (λ h, (h.1, sh h.1 P ∥ h.2)) (heads Q)
  | PG g => gheads g
  | _ => []
  end.

Definition resp (a : coact) (h : prefix * proc) : option proc :=
  match h.1, a with
  | PRecv k' c', CoIn k c v => if decide (k = k' ∧ c = c') then Some (h.2 ⟦ v ⟧) else None
  | POp k' E' es, CoOp k E qs =>
      if decide (k = k' ∧ E = E' ∧ eval_qubits es = Some qs) then Some h.2 else None
  | PMeas k' M' es, CoMeas k M qs n =>
      if decide (k = k' ∧ M = M' ∧ eval_qubits es = Some qs) then Some (h.2 ⟦ VNat n ⟧) else None
  | PInit k' es, CoInit k qs => if decide (k = k' ∧ eval_qubits es = Some qs) then Some h.2 else None
  | _, _ => None
  end.

Lemma gco_heads g a : gco_succ g a = omap (resp a) (gheads g).
Proof.
  induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl.
  - done.
  - done.
  - unfold resp. destruct 𝜆, a; simpl; try done; by case_decide.
  - by rewrite omap_app, IH1, IH2.
Qed.

Lemma omap_map_fmap {A B C} (f : A → option B) (g : A → A) (k : B → C) (f' : A → option C) (l : list A) :
  (∀ x, f' (g x) = k <$> f x) → omap f' (map g l) = k <$> omap f l.
Proof.
  intros Hfg. induction l as [|x l IH]; [done|]. csimpl. rewrite Hfg. destruct (f x); csimpl; by rewrite IH.
Qed.

Lemma resp_parL a Q l :
  omap (resp a) (map (λ h : prefix * proc, (h.1, h.2 ∥ sh h.1 Q)) l) = (λ P', P' ∥ Q) <$> omap (resp a) l.
Proof.
  apply omap_map_fmap. intros [𝜆 D]. unfold resp, sh.
  destruct 𝜆, a; simpl; try done; case_decide; simpl; by rewrite ?subst_shiftv.
Qed.

Lemma resp_parR a P l :
  omap (resp a) (map (λ h : prefix * proc, (h.1, sh h.1 P ∥ h.2)) l) = (λ Q', P ∥ Q') <$> omap (resp a) l.
Proof.
  apply omap_map_fmap. intros [𝜆 D]. unfold resp, sh.
  destruct 𝜆, a; simpl; try done; case_decide; simpl; by rewrite ?subst_shiftv.
Qed.

Lemma co_heads Z a : (∀ k c v, a ≠ CoOut k c v) → co_succ Z a = omap (resp a) (heads Z).
Proof.
  intros Ha. induction Z as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl.
  - destruct a; try done. by destruct (Ha k c0 v).
  - destruct (eval e) as [[[]| |]|]; done.
  - by rewrite omap_app, resp_parL, resp_parR, IHP, IHQ.
  - done.
  - done.
  - done.
  - apply gco_heads.
Qed.

Definition chain (vs : list val) (A : val → proc) (d : proc) : proc :=
  foldr (λ v acc, PIte (EEq (EVar 0) (EVal v)) (shiftv 0 (A v)) acc) d vs.

Lemma chain_tite vs A d w :
  (w ∈ vs ∧ tite (A w) ((chain vs A d) ⟦ w ⟧)) ∨ (w ∉ vs ∧ tite (d ⟦ w ⟧) ((chain vs A d) ⟦ w ⟧)).
Proof.
  induction vs as [|v vs IH].
  - right. split; [intros Hin; by apply elem_of_nil in Hin|apply ti_refl].
  - simpl. rewrite subst_shiftv. destruct (decide (w = v)) as [->|Hne].
    + left. split; [by left|]. apply ti_T; [|apply ti_refl]. simpl. by rewrite bool_decide_eq_true_2.
    + destruct IH as [[Hin IH]|[Hnin IH]]; [left|right].
      * split; [by right|]. apply ti_F; [|exact IH]. simpl. by rewrite bool_decide_eq_false_2.
      * split; [intros Hin; apply elem_of_cons in Hin as [E|Hin]; [by destruct Hne|by destruct Hnin]|].
        apply ti_F; [|exact IH]. simpl. by rewrite bool_decide_eq_false_2.
Qed.

Definition gsum (l : list guard) : guard := foldr GSum (GNil []) l.

Lemma gco_gsum l a : gco_succ (gsum l) a = concat (map (λ g, gco_succ g a) l).
Proof. induction l as [|g l IH]; [done|]. simpl. by rewrite IH. Qed.

Definition rg (o : offer) : option guard :=
  match o with
  | OffOut _ _ _ => None
  | OffIn k c => Some (PRecv k c ∙ PG ①)
  | OffOp k E qs => Some (POp k E (quote qs) ∙ PG ①)
  | OffMeas k M qs => Some (PMeas k M (quote qs) ∙ PG ①)
  | OffInit k qs => Some (PInit k (quote qs) ∙ PG ①)
  end.

Definition co_of (o : offer) : coact :=
  match o with
  | OffOut k c v => CoOut k c v
  | OffIn k c => CoIn k c (VBool true)
  | OffOp k E qs => CoOp k E qs
  | OffMeas k M qs => CoMeas k M qs 0
  | OffInit k qs => CoInit k qs
  end.

Section Head.
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).

  Definition kont (rec : node → proc → proc) (m : node) (o : offer) (a : coact) (Z' : proc) : proc :=
    if wrapb m o then PG ① ∥ Z' else rec (m ++ [a]) Z'.

  Definition dflt (m : node) (o : offer) (D : proc) : proc := if wrapb m o then PG ① ∥ D else D.

  Definition hguard (rec : node → proc → proc) (m : node) (h : prefix * proc) : option guard :=
    match h.1 with
    | PTau _ => None
    | PRecv k c =>
        Some (PRecv k c ∙ chain VL (λ v, kont rec m (OffIn k c) (CoIn k c v) (h.2 ⟦ v ⟧)) (dflt m (OffIn k c) h.2))
    | POp k E es =>
        match eval_qubits es with
        | Some qs => Some (POp k E (quote qs) ∙ kont rec m (OffOp k E qs) (CoOp k E qs) h.2)
        | None => None
        end
    | PMeas k M es =>
        match eval_qubits es with
        | Some qs =>
            Some (PMeas k M (quote qs) ∙
                    chain VL (λ v, match v with
                                   | VNat n => kont rec m (OffMeas k M qs) (CoMeas k M qs n) (h.2 ⟦ v ⟧)
                                   | _ => 𝟘
                                   end) (dflt m (OffMeas k M qs) h.2))
        | None => None
        end
    | PInit k es =>
        match eval_qubits es with
        | Some qs => Some (PInit k (quote qs) ∙ kont rec m (OffInit k qs) (CoInit k qs) h.2)
        | None => None
        end
    end.

  Definition free_rep (Z : proc) (o : offer) : bool :=
    match omap (resp (co_of o)) (heads Z) with [] => true | _ => false end.

  Definition repl (m : node) (Z : proc) : list offer := filter (λ o, free_rep Z o = true) (reps m).

  Definition hsum (rec : node → proc → proc) (m : node) (Z : proc) : guard :=
    gsum (omap (hguard rec m) (heads Z) ++ omap rg (repl m Z)).

  Fixpoint tn (f : nat) (m : node) (X : proc) : proc :=
    match f with
    | 0 => X
    | S f' => if successb X then X else bagof X ∥ PG (hsum (tn f') m (ns X))
    end.

  Definition unlisted (a : coact) : Prop :=
    match a with
    | CoIn _ _ v => v ∉ VL
    | CoMeas _ _ _ n => VNat n ∉ VL
    | _ => False
    end.

  Definition hres (rec : node → proc → proc) (m : node) (a : coact) (Z' Y' : proc) : Prop :=
    ∃ W, tite W Y'
      ∧ ((wrapb m (offer_of a) = true ∧ W = PG ① ∥ Z')
         ∨ (wrapb m (offer_of a) = false ∧ (W = rec (m ++ [a]) Z' ∨ (W = Z' ∧ unlisted a)))).

  Lemma kont_hres rec m a Z' : hres rec m a Z' (kont rec m (offer_of a) a Z').
  Proof.
    exists (kont rec m (offer_of a) a Z'). split; [apply ti_refl|]. unfold kont.
    destruct (wrapb m (offer_of a)); [left; by split|right; split; [done|by left]].
  Qed.

  Lemma hguard_spec rec m h a :
    match hguard rec m h with
    | None => resp a h = None
    | Some g => (resp a h = None ∧ gco_succ g a = [])
               ∨ ∃ Z' Y', resp a h = Some Z' ∧ gco_succ g a = [Y'] ∧ hres rec m a Z' Y'
    end.
  Proof.
    destruct h as [𝜆 D]. unfold hguard, resp. destruct 𝜆 as [t|t c|t E es|t M es|t es]; simpl.
    - by destruct a.
    - destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try (left; by split).
      destruct (decide (k = t ∧ c0 = c)) as [[-> ->]|Hd]; [|left; by split].
      right. eexists _, _. split; [done|]. split; [done|].
      destruct (chain_tite VL (λ v, kont rec m (OffIn t c) (CoIn t c v) (D ⟦ v ⟧)) (dflt m (OffIn t c) D) v) as [[_ Ht]|[Hu Ht]].
      + exists (kont rec m (OffIn t c) (CoIn t c v) (D ⟦ v ⟧)). split; [exact Ht|]. unfold kont. simpl.
        destruct (wrapb m (OffIn t c)); [left; by split|right; split; [done|by left]].
      + exists (dflt m (OffIn t c) D ⟦ v ⟧). split; [exact Ht|]. unfold dflt. simpl.
        destruct (wrapb m (OffIn t c)); [left; by split|right; split; [done|right; by split]].
    - destruct (eval_qubits es) as [qs0|] eqn:Eq.
      + destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try (left; by split). simpl. rewrite eval_quote.
        destruct (decide (k = t ∧ E0 = E ∧ Some qs0 = Some qs)) as [(-> & -> & [= ->])|Hd]; [|left; by split].
        right. eexists _, _. split; [done|]. split; [done|]. exact (kont_hres rec m (CoOp t E qs) D).
      + destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try done.
        case_decide as Hd; [|done]. by destruct Hd as (_ & _ & ?).
    - destruct (eval_qubits es) as [qs0|] eqn:Eq.
      + destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try (left; by split). simpl. rewrite eval_quote.
        destruct (decide (k = t ∧ M0 = M ∧ Some qs0 = Some qs)) as [(-> & -> & [= ->])|Hd]; [|left; by split].
        right. eexists _, _. split; [done|]. split; [done|].
        destruct (chain_tite VL (λ v, match v with
                                      | VNat n0 => kont rec m (OffMeas t M qs) (CoMeas t M qs n0) (D ⟦ v ⟧)
                                      | _ => 𝟘
                                      end) (dflt m (OffMeas t M qs) D) (VNat n)) as [[_ Ht]|[Hu Ht]].
        * exists (kont rec m (OffMeas t M qs) (CoMeas t M qs n) (D ⟦ VNat n ⟧)). split; [exact Ht|]. unfold kont. simpl.
          destruct (wrapb m (OffMeas t M qs)); [left; by split|right; split; [done|by left]].
        * exists (dflt m (OffMeas t M qs) D ⟦ VNat n ⟧). split; [exact Ht|]. unfold dflt. simpl.
          destruct (wrapb m (OffMeas t M qs)); [left; by split|right; split; [done|right; by split]].
      + destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try done.
        case_decide as Hd; [|done]. by destruct Hd as (_ & _ & ?).
    - destruct (eval_qubits es) as [qs0|] eqn:Eq.
      + destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try (left; by split). simpl. rewrite eval_quote.
        destruct (decide (k = t ∧ Some qs0 = Some qs)) as [(-> & [= ->])|Hd]; [|left; by split].
        right. eexists _, _. split; [done|]. split; [done|]. exact (kont_hres rec m (CoInit t qs) D).
      + destruct a as [k c0 v|k c0 v|k E0 qs|k M0 qs n|k qs]; try done.
        case_decide as Hd; [|done]. by destruct Hd as (_ & ?).
  Qed.
End Head.
(* end hide *)
