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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Head.
  Context `{lqP : lqCCS_Parameters}.

Inductive tite (W : prog) : prog → Prop :=
| ti_refl : tite W W
| ti_T e Y A : 〚 e 〛 = true → tite W Y → tite W (If e Then Y Else A)
| ti_F e Y A : 〚 e 〛 = false → tite W Y → tite W (If e Then A Else Y).

Fixpoint gheads (g : guard) : list (prefix * prog) :=
  match g with
  | 𝟘{_} | 𝟙 => []
  | π ∙ P => [(π, P)]
  | (g1 + g2)%lq => gheads g1 ++ gheads g2
  end.

Definition sh (π : prefix) (Q : prog) : prog := Nat.iter (prefix_binds π) ⇧ᵥ Q.

Fixpoint heads (Z : prog) : list (prefix * prog) :=
  match Z with
  | If e Then P Else Q =>
      match eval e with
      | Some (VBool true) => heads P
      | Some (VBool false) => heads Q
      | _ => []
      end
  | P ∥ Q => map (λ h, (h.1, h.2 ∥ sh h.1 Q)) (heads P) ++ map (λ h, (h.1, sh h.1 P ∥ h.2)) (heads Q)
  | PG g => gheads g
  | _ => []
  end.

Definition resp (a : coact) (h : prefix * prog) : option prog :=
  match h.1, a with
  | (t' ∶ c' ?), CoIn t c v => if decide (t = t' ∧ c = c') then Some (h.2 ⁅ v ⁆ᵥ) else None
  | (t' ∶ U' ⦅es⦆), CoOp t U qs =>
      if decide (t = t' ∧ U = U' ∧ eval_qubits es = Some qs) then Some h.2 else None
  | (t' ∶ M' ⦅es ▷⦆), CoMeas t M qs n =>
      if decide (t = t' ∧ M = M' ∧ eval_qubits es = Some qs) then Some (h.2 ⁅ VNat n ⁆ᵥ) else None
  | (t' ∶ e := |0⟩), CoInit t q => if decide (t = t' ∧ eval_qubit e = Some q) then Some h.2 else None
  | _, _ => None
  end.

Lemma gco_heads g a : gco_succ g a = omap (resp a) (gheads g).
Proof.
  induction g as [es| |π P|g1 IH1 g2 IH2]; simpl.
  - done.
  - done.
  - unfold resp. destruct π, a; simpl; try done; by case_decide.
  - by rewrite omap_app, IH1, IH2.
Qed.

Lemma omap_map_fmap {A B C} (f : A → option B) (g : A → A) (h : B → C) (f' : A → option C) (l : list A) :
  (∀ x, f' (g x) = h <$> f x) → omap f' (map g l) = h <$> omap f l.
Proof.
  intros Hfg. induction l as [|x l IH]; [done|]. csimpl. rewrite Hfg. destruct (f x); csimpl; by rewrite IH.
Qed.

Lemma resp_parL a Q l :
  omap (resp a) (map (λ h : prefix * prog, (h.1, h.2 ∥ sh h.1 Q)) l) = (λ P', P' ∥ Q) <$> omap (resp a) l.
Proof.
  apply omap_map_fmap. intros [π D]. unfold resp, sh.
  destruct π, a; simpl; try done; case_decide; simpl; by rewrite ?subst_shiftv.
Qed.

Lemma resp_parR a P l :
  omap (resp a) (map (λ h : prefix * prog, (h.1, sh h.1 P ∥ h.2)) l) = (λ Q', P ∥ Q') <$> omap (resp a) l.
Proof.
  apply omap_map_fmap. intros [π D]. unfold resp, sh.
  destruct π, a; simpl; try done; case_decide; simpl; by rewrite ?subst_shiftv.
Qed.

Lemma co_heads Z a : (∀ t c v, a ≠ CoOut t c v) → obsb Z = true → co_succ Z a = omap (resp a) (heads Z).
Proof.
  intros Ha. induction Z as [t' c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t' P IHP|g]; simpl; intros Hob.
  - destruct a; try done. by destruct (Ha t c0 v).
  - apply andb_prop in Hob as [HP HQ]. destruct (eval e) as [[[]| |]|]; auto.
  - apply andb_prop in Hob as [HP HQ]. by rewrite omap_app, resp_parL, resp_parR, IHP, IHQ.
  - done.
  - done.
  - discriminate Hob.
  - apply gco_heads.
Qed.

Definition chain (vs : list val) (A : val → prog) (d : prog) : prog :=
  foldr (λ (v : val) acc, (If (#0 =ₑ v) Then ⇧ᵥ (A v) Else acc)) d vs.

Lemma chain_tite vs A d w :
  (w ∈ vs ∧ tite (A w) ((chain vs A d) ⁅ w ⁆ᵥ)) ∨ (w ∉ vs ∧ tite (d ⁅ w ⁆ᵥ) ((chain vs A d) ⁅ w ⁆ᵥ)).
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

Definition gsum (l : list guard) : guard := foldr GSum 𝟘{ [] } l.

Lemma gco_gsum l a : gco_succ (gsum l) a = concat (map (λ g, gco_succ g a) l).
Proof. induction l as [|g l IH]; [done|]. simpl. by rewrite IH. Qed.

Definition rg (o : offer) : option guard :=
  match o with
  | OffOut _ _ _ => None
  | OffIn t c => Some ((t ∶ c ?) ∙ PG 𝟙)
  | OffOp t U qs => Some ((t ∶ U ⦅quote qs⦆) ∙ PG 𝟙)
  | OffMeas t M qs => Some ((t ∶ M ⦅quote qs ▷⦆) ∙ PG 𝟙)
  | OffInit t q => Some ((t ∶ $q := |0⟩) ∙ PG 𝟙)
  | OffUnfold _ => None
  end.

Definition co_of (o : offer) : coact :=
  match o with
  | OffOut t c v => CoOut t c v
  | OffIn t c => CoIn t c true
  | OffOp t U qs => CoOp t U qs
  | OffMeas t M qs => CoMeas t M qs 0
  | OffInit t q => CoInit t q
  | OffUnfold t => CoUnfold t
  end.

Section Head_Observer.
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).

  Definition kont (rec : node → prog → prog) (z : node) (o : offer) (a : coact) (Z' : prog) : prog :=
    if wrapb z o then PG 𝟙 ∥ Z' else rec (z ++ [a]) Z'.

  Definition dflt (z : node) (o : offer) (D : prog) : prog := if wrapb z o then PG 𝟙 ∥ D else D.

  Definition hguard (rec : node → prog → prog) (z : node) (h : prefix * prog) : option guard :=
    match h.1 with
    | _ ∶ 𝛕 => None
    | t ∶ c ? =>
        Some ((t ∶ c ?) ∙ chain VL (λ v, kont rec z (OffIn t c) (CoIn t c v) (h.2 ⁅ v ⁆ᵥ)) (dflt z (OffIn t c) h.2))
    | t ∶ U ⦅es⦆ =>
        match eval_qubits es with
        | Some qs => Some ((t ∶ U ⦅quote qs⦆) ∙ kont rec z (OffOp t U qs) (CoOp t U qs) h.2)
        | None => None
        end
    | t ∶ M ⦅es ▷⦆ =>
        match eval_qubits es with
        | Some qs =>
            Some ((t ∶ M ⦅quote qs ▷⦆) ∙
                    chain VL (λ v, match v with
                                   | VNat n => kont rec z (OffMeas t M qs) (CoMeas t M qs n) (h.2 ⁅ v ⁆ᵥ)
                                   | _ => 𝟘
                                   end) (dflt z (OffMeas t M qs) h.2))
        | None => None
        end
    | t ∶ e := |0⟩ =>
        match eval_qubit e with
        | Some q => Some ((t ∶ $q := |0⟩) ∙ kont rec z (OffInit t q) (CoInit t q) h.2)
        | None => None
        end
    end.

  Definition free_rep (Z : prog) (o : offer) : bool :=
    match omap (resp (co_of o)) (heads Z) with [] => true | _ => false end.

  Definition repl (z : node) (Z : prog) : list offer := filter (λ o, free_rep Z o = true) (reps z).

  Definition hsum (rec : node → prog → prog) (z : node) (Z : prog) : guard :=
    gsum (omap (hguard rec z) (heads Z) ++ omap rg (repl z Z)).

  Fixpoint tn (f : nat) (z : node) (X : prog) : prog :=
    match f with
    | 0 => X
    | S f' => if successb X then X else bagof X ∥ PG (hsum (tn f') z (ns X))
    end.

  Definition unlisted (a : coact) : Prop :=
    match a with
    | CoIn _ _ v => v ∉ VL
    | CoMeas _ _ _ n => VNat n ∉ VL
    | _ => False
    end.

  Definition hres (rec : node → prog → prog) (z : node) (a : coact) (Z' Y' : prog) : Prop :=
    ∃ W, tite W Y'
      ∧ ((wrapb z (offer_of a) = true ∧ W = PG 𝟙 ∥ Z')
         ∨ (wrapb z (offer_of a) = false ∧ (W = rec (z ++ [a]) Z' ∨ (W = Z' ∧ unlisted a)))).

  Lemma kont_hres rec z a Z' : hres rec z a Z' (kont rec z (offer_of a) a Z').
  Proof.
    exists (kont rec z (offer_of a) a Z'). split; [apply ti_refl|]. unfold kont.
    destruct (wrapb z (offer_of a)); [left; by split|right; split; [done|by left]].
  Qed.

  Lemma hguard_spec rec z h a :
    match hguard rec z h with
    | None => resp a h = None
    | Some g => (resp a h = None ∧ gco_succ g a = [])
               ∨ ∃ Z' Y', resp a h = Some Z' ∧ gco_succ g a = [Y'] ∧ hres rec z a Z' Y'
    end.
  Proof.
    destruct h as [π D]. unfold hguard, resp. destruct π as [t'|t' c|t' U es|t' M es|t' e]; simpl.
    - by destruct a.
    - destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try (left; by split).
      destruct (decide (t = t' ∧ c0 = c)) as [[-> ->]|Hd]; [|left; by split].
      right. eexists _, _. split; [done|]. split; [done|].
      destruct (chain_tite VL (λ v, kont rec z (OffIn t' c) (CoIn t' c v) (D ⁅ v ⁆ᵥ)) (dflt z (OffIn t' c) D) v) as [[_ Ht]|[Hu Ht]].
      + exists (kont rec z (OffIn t' c) (CoIn t' c v) (D ⁅ v ⁆ᵥ)). split; [exact Ht|]. unfold kont. simpl.
        destruct (wrapb z (OffIn t' c)); [left; by split|right; split; [done|by left]].
      + exists (dflt z (OffIn t' c) D ⁅ v ⁆ᵥ). split; [exact Ht|]. unfold dflt. simpl.
        destruct (wrapb z (OffIn t' c)); [left; by split|right; split; [done|right; by split]].
    - destruct (eval_qubits es) as [qs0|] eqn:Eq.
      + destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try (left; by split). simpl. rewrite eval_quote.
        destruct (decide (t = t' ∧ U0 = U ∧ Some qs0 = Some qs)) as [(-> & -> & [= ->])|Hd]; [|left; by split].
        right. eexists _, _. split; [done|]. split; [done|]. exact (kont_hres rec z (CoOp t' U qs) D).
      + destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try done.
        case_decide as Hd; [|done]. by destruct Hd as (_ & _ & ?).
    - destruct (eval_qubits es) as [qs0|] eqn:Eq.
      + destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try (left; by split). simpl. rewrite eval_quote.
        destruct (decide (t = t' ∧ M0 = M ∧ Some qs0 = Some qs)) as [(-> & -> & [= ->])|Hd]; [|left; by split].
        right. eexists _, _. split; [done|]. split; [done|].
        destruct (chain_tite VL (λ v, match v with
                                      | VNat n0 => kont rec z (OffMeas t' M qs) (CoMeas t' M qs n0) (D ⁅ v ⁆ᵥ)
                                      | _ => 𝟘
                                      end) (dflt z (OffMeas t' M qs) D) (VNat n)) as [[_ Ht]|[Hu Ht]].
        * exists (kont rec z (OffMeas t' M qs) (CoMeas t' M qs n) (D ⁅ VNat n ⁆ᵥ)). split; [exact Ht|]. unfold kont. simpl.
          destruct (wrapb z (OffMeas t' M qs)); [left; by split|right; split; [done|by left]].
        * exists (dflt z (OffMeas t' M qs) D ⁅ VNat n ⁆ᵥ). split; [exact Ht|]. unfold dflt. simpl.
          destruct (wrapb z (OffMeas t' M qs)); [left; by split|right; split; [done|right; by split]].
      + destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try done.
        case_decide as Hd; [|done]. by destruct Hd as (_ & _ & ?).
    - destruct (eval_qubit e) as [q0|] eqn:Eq.
      + destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try (left; by split). simpl. change (eval_qubit $q0) with (Some q0).
        destruct (decide (t = t' ∧ Some q0 = Some q)) as [(-> & [= ->])|Hd]; [|left; by split].
        right. eexists _, _. split; [done|]. split; [done|]. exact (kont_hres rec z (CoInit t' q) D).
      + destruct a as [t c0 v|t c0 v|t U0 qs|t M0 qs n|t q|t]; try done.
        case_decide as Hd; [|done]. by destruct Hd as (_ & ?).
  Qed.
End Head_Observer.

End Head.

(* end hide *)
