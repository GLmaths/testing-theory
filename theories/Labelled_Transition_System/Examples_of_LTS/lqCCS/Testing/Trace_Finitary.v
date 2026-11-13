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
(* end hide *)
(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
From Stdlib.Bool Require Import Bool.
From Stdlib.Logic Require Import Classical.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Truncation lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Trace_Complete lqCCS.Testing.Trace_Sound lqCCS.Testing.Trace_Convergence.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Pool.
  Context `{QM : QuantumModel} (V : val → Prop) (MM : meas → Prop) (L : nat).

  Fixpoint oke (e : exp) : Prop :=
    match e with
    | EVar _ => True
    | EVal v => V v
    | ENot e => oke e
    | EOr a b | ELe a b | EEq a b => oke a ∧ oke b
    end.

  Definition okpre (𝜆 : prefix) : Prop :=
    match 𝜆 with
    | PTau _ | PRecv _ _ => True
    | POp _ _ es | PInit _ es => Forall oke es
    | PMeas _ M es => Forall oke es ∧ MM M ∧ length es ≤ L
    end.

  Fixpoint ok (P : proc) : Prop :=
    match P with
    | PSend _ _ e => oke e
    | PIte e P Q => oke e ∧ ok P ∧ ok Q
    | P ∥ Q => ok P ∧ ok Q
    | ν P | PRec _ _ P => ok P
    | PVar _ => True
    | PG g => gok g
    end
  with gok (g : guard) : Prop :=
    match g with
    | GNil es => Forall oke es
    | ① => True
    | 𝜆 ∙ P => okpre 𝜆 ∧ ok P
    | (g1 + g2)%lq => gok g1 ∧ gok g2
    end.

  Hypothesis HVb : ∀ b, V (VBool b).
  Hypothesis HVm : ∀ M qs (k' : Out (meas_of M qs)),
    MM M → length qs ≤ L → Forall (λ x, V (VQubit x)) qs → V (VNat (code _ k')).

  Lemma oke_eval e v : oke e → eval e = Some v → V v.
  Proof.
    revert v. induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; intros v Ho He.
    - discriminate He.
    - by injection He as <-.
    - destruct (eval e) as [[b| |]|]; try discriminate He. injection He as <-. apply HVb.
    - destruct (eval e1) as [[b1| |]|]; try discriminate He. destruct (eval e2) as [[b2| |]|]; try discriminate He.
      injection He as <-. apply HVb.
    - destruct (eval e1) as [v1|]; [|discriminate He]. destruct (eval e2) as [v2|]; [|discriminate He].
      destruct (val_le v1 v2); simpl in He; [|discriminate He]. injection He as <-. apply HVb.
    - destruct (eval e1) as [v1|]; [|discriminate He]. destruct (eval e2) as [v2|]; [|discriminate He].
      injection He as <-. apply HVb.
  Qed.

  Lemma oke_subst k v e : V v → oke e → oke (exp_subst k v e).
  Proof.
    intros Hv. induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; try tauto.
    intros _. repeat case_decide; simpl; done.
  Qed.

  Lemma oke_shift k e : oke e → oke (exp_shift k e).
  Proof.
    induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; try tauto.
    intros _. repeat case_decide; simpl; done.
  Qed.

  Lemma okes_subst k v es : V v → Forall oke es → Forall oke (map (exp_subst k v) es).
  Proof. intros Hv Hes. apply Forall_map. eapply Forall_impl; [exact Hes|]. intros e. by apply oke_subst. Qed.

  Lemma okes_shift k es : Forall oke es → Forall oke (map (exp_shift k) es).
  Proof. intros Hes. apply Forall_map. eapply Forall_impl; [exact Hes|]. intros e. by apply oke_shift. Qed.

  Lemma okpre_subst k v 𝜆 : V v → okpre 𝜆 → okpre (prefix_subst k v 𝜆).
  Proof.
    intros Hv. destruct 𝜆 as [t|t c|t E es|t M es|t es]; simpl; try done.
    - by apply okes_subst.
    - intros (Ho & Hm & Hl). rewrite length_map. split; [by apply okes_subst|done].
    - by apply okes_subst.
  Qed.

  Lemma okpre_shift k 𝜆 : okpre 𝜆 → okpre (prefix_shift k 𝜆).
  Proof.
    destruct 𝜆 as [t|t c|t E es|t M es|t es]; simpl; try done.
    - by apply okes_shift.
    - intros (Ho & Hm & Hl). rewrite length_map. split; [by apply okes_shift|done].
    - by apply okes_shift.
  Qed.

  Lemma ok_subst v : V v → (∀ P k, ok P → ok (subst k v P)) ∧ (∀ g k, gok g → gok (gsubst k v g)).
  Proof.
    intros Hv. apply proc_guard_ind; simpl.
    - intros t c e k Ho. by apply oke_subst.
    - intros e P IHP Q IHQ k (He & HP & HQ). split; [by apply oke_subst|]. split; auto.
    - intros P IHP Q IHQ k [HP HQ]. split; auto.
    - intros P IHP k HP. auto.
    - done.
    - intros t X P IHP k HP. auto.
    - intros g IHg k Hg. auto.
    - intros es k Ho. by apply okes_subst.
    - done.
    - intros 𝜆 P IHP k [Ha Hb]. split; [by apply okpre_subst|auto].
    - intros g1 IH1 g2 IH2 k [Ha Hb]. split; auto.
  Qed.

  Lemma ok_shiftv : (∀ P k, ok P → ok (shiftv k P)) ∧ (∀ g k, gok g → gok (gshiftv k g)).
  Proof.
    apply proc_guard_ind; simpl.
    - intros t c e k Ho. by apply oke_shift.
    - intros e P IHP Q IHQ k (He & HP & HQ). split; [by apply oke_shift|]. split; auto.
    - intros P IHP Q IHQ k [HP HQ]. split; auto.
    - intros P IHP k HP. auto.
    - done.
    - intros t X P IHP k HP. auto.
    - intros g IHg k Hg. auto.
    - intros es k Ho. by apply okes_shift.
    - done.
    - intros 𝜆 P IHP k [Ha Hb]. split; [by apply okpre_shift|auto].
    - intros g1 IH1 g2 IH2 k [Ha Hb]. split; auto.
  Qed.

  Lemma ok_ren : (∀ P f, ok P → ok (ren f P)) ∧ (∀ g f, gok g → gok (gren f g)).
  Proof.
    apply proc_guard_ind; simpl.
    - intros t c e f Ho. exact Ho.
    - intros e P IHP Q IHQ f (He & HP & HQ). split; [done|]. split; auto.
    - intros P IHP Q IHQ f [HP HQ]. split; auto.
    - intros P IHP f HP. auto.
    - intros X f _. exact Logic.I.
    - intros t X P IHP f HP. auto.
    - intros g IHg f Hg. auto.
    - intros es f Ho. exact Ho.
    - intros f _. exact Logic.I.
    - intros 𝜆 P IHP f [Ha Hb]. split; [by destruct 𝜆|auto].
    - intros g1 IH1 g2 IH2 f [Ha Hb]. split; auto.
  Qed.

  Lemma ok_iter n Q : ok Q → ok (Nat.iter n (shiftv 0) Q).
  Proof. intros HQ. induction n as [|n IH]; simpl; [done|]. by apply (proj1 ok_shiftv). Qed.

  Lemma ok_prsubst :
    (∀ P X Q, ok P → ok Q → ok (pr_subst X P Q)) ∧ (∀ g X Q, gok g → ok Q → gok (gpr_subst X g Q)).
  Proof.
    apply proc_guard_ind; simpl.
    - intros t c e X R Ho _. exact Ho.
    - intros e P IHP Q IHQ X R (He & HP & HQ) HR. split; [done|]. split; auto.
    - intros P IHP Q IHQ X R [HP HQ] HR. split; auto.
    - intros P IHP X R HP HR. apply IHP; [done|]. by apply (proj1 ok_ren).
    - intros Y X R _ HR. by case_decide.
    - intros t Y P IHP X R HP HR. case_decide; simpl; auto.
    - intros g IHg X R Hg HR. auto.
    - intros es X R Ho _. exact Ho.
    - intros X R _ _. exact Logic.I.
    - intros 𝜆 P IHP X R [Ha Hb] HR. split; [done|]. apply IHP; [done|]. by apply ok_iter.
    - intros g1 IH1 g2 IH2 X R [Ha Hb] HR. split; auto.
  Qed.

  Definition lok (l : Labels prog_action) : Prop :=
    match l with
    | ActExt (PrIn _ v) => V v
    | ActExt (PrMeas _ _ n) => V (VNat n)
    | _ => True
    end.

  Definition mq (M : meas) (qs : list qubit) : Prop :=
    MM M ∧ length qs ≤ L ∧ Forall (λ x, V (VQubit x)) qs.

  Lemma evq es qs : Forall oke es → eval_qubits es = Some qs →
    length qs = length es ∧ Forall (λ x, V (VQubit x)) qs.
  Proof.
    intros Ho He. apply mapM_Some in He. induction He as [|e x es qs Hex _ IH]; [by split|].
    apply Forall_cons in Ho as [Ho1 Ho2]. destruct (IH Ho2) as [Hl Hf]. split; [simpl; by rewrite Hl|].
    constructor; [|done]. unfold eval_qubit in Hex. destruct (eval e) as [[b|n|x0]|] eqn:Ee; try discriminate Hex.
    injection Hex as <-. exact (oke_eval e _ Ho1 Ee).
  Qed.

  Lemma gstep_noout g s c v P' : ¬ prog_gstep g s (ActExt (PrOut c v)) P'.
  Proof.
    intros Hs. remember (ActExt (PrOut c v)) as l eqn:El. induction Hs using prog_gstep_ind; try discriminate El; auto.
  Qed.

  Lemma step_out P s l P' : ok P → prog_step P s l P' → ∀ c v, l = ActExt (PrOut c v) → V v.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hs IH|e P Q s l Q' He Hs IH
      |P Q s l P' Hs IH|P Q s l Q' Hs IH|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
      |P s l P' Hs IH|t X P] using prog_step_guard_ind; simpl; intros Ho c0 v0 El.
    - subst l. exfalso. exact (gstep_noout _ _ _ _ _ Hg).
    - injection El as _ <-. exact (oke_eval e v Ho He).
    - exact (IH (proj1 (proj2 Ho)) c0 v0 El).
    - exact (IH (proj2 (proj2 Ho)) c0 v0 El).
    - exact (IH (proj1 Ho) c0 v0 El).
    - exact (IH (proj2 Ho) c0 v0 El).
    - discriminate El.
    - discriminate El.
    - subst l. exact (IH Ho _ v0 eq_refl).
    - discriminate El.
  Qed.

  Lemma gstep_meas g s l P' : gok g → prog_gstep g s l P' → ∀ M qs n, l = ActExt (PrMeas M qs n) → mq M qs.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [t P|t c v P|t E es qs P He|t M es qs n P He|t es qs P He
      |g1 g2 s l P' Hs IH|g1 g2 s l P' Hs IH] using prog_gstep_ind; simpl; intros Ho M0 qs0 n0 El; try discriminate El.
    - injection El as <- <- <-. destruct Ho as [(Hes & Hm & Hl) _]. destruct (evq es qs Hes He) as [Hlen Hf].
      split; [done|]. split; [lia|done].
    - exact (IH (proj1 Ho) M0 qs0 n0 El).
    - exact (IH (proj2 Ho) M0 qs0 n0 El).
  Qed.

  Lemma step_meas P s l P' : ok P → prog_step P s l P' → ∀ M qs n, l = ActExt (PrMeas M qs n) → mq M qs.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hs IH|e P Q s l Q' He Hs IH
      |P Q s l P' Hs IH|P Q s l Q' Hs IH|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
      |P s l P' Hs IH|t X P] using prog_step_guard_ind; simpl; intros Ho M0 qs0 n0 El; try discriminate El.
    - exact (gstep_meas g s l P' Ho Hg M0 qs0 n0 El).
    - exact (IH (proj1 (proj2 Ho)) M0 qs0 n0 El).
    - exact (IH (proj2 (proj2 Ho)) M0 qs0 n0 El).
    - exact (IH (proj1 Ho) M0 qs0 n0 El).
    - exact (IH (proj2 Ho) M0 qs0 n0 El).
    - subst l. exact (IH Ho M0 qs0 n0 eq_refl).
  Qed.

  Lemma gstep_ok g s l P' : gok g → prog_gstep g s l P' → lok l → ok P'.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [t P|t c v P|t E es qs P He|t M es qs n P He|t es qs P He
      |g1 g2 s l P' Hs IH|g1 g2 s l P' Hs IH] using prog_gstep_ind; simpl; intros Ho Hl.
    - exact (proj2 Ho).
    - exact (proj1 (ok_subst v Hl) P 0 (proj2 Ho)).
    - exact (proj2 Ho).
    - exact (proj1 (ok_subst (VNat n) Hl) P 0 (proj2 Ho)).
    - exact (proj2 Ho).
    - exact (IH (proj1 Ho) Hl).
    - exact (IH (proj2 Ho) Hl).
  Qed.

  Lemma lok_ren l : lok (ren_lbl Datatypes.S l) ↔ lok l.
  Proof. destruct l as [[]|]; done. Qed.

  Lemma step_ok P s l P' : ok P → prog_step P s l P' → lok l → ok P'.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [g s l P' Hg|t c e v He|e P Q s l P' He Hs IH|e P Q s l Q' He Hs IH
      |P Q s l P' Hs IH|P Q s l Q' Hs IH|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
      |P s l P' Hs IH|t X P] using prog_step_guard_ind; simpl; intros Ho Hl.
    - exact (gstep_ok g s l P' Ho Hg Hl).
    - constructor.
    - exact (IH (proj1 (proj2 Ho)) Hl).
    - exact (IH (proj2 (proj2 Ho)) Hl).
    - split; [exact (IH (proj1 Ho) Hl)|exact (proj2 Ho)].
    - split; [exact (proj1 Ho)|exact (IH (proj2 Ho) Hl)].
    - pose proof (step_out P _ _ P' (proj1 Ho) Hs1 c v eq_refl) as Hv.
      split; [exact (IH1 (proj1 Ho) Logic.I)|exact (IH2 (proj2 Ho) Hv)].
    - pose proof (step_out Q _ _ Q' (proj2 Ho) Hs2 c v eq_refl) as Hv.
      split; [exact (IH1 (proj1 Ho) Hv)|exact (IH2 (proj2 Ho) Logic.I)].
    - apply IH; [done|]. by apply lok_ren.
    - apply (proj1 ok_prsubst); done.
  Qed.

  Context (q : proc * St) (O : node → list msg) (T : proc) (r : nat → dist comp) (w : nat → item).
  Hypothesis HO : ∀ n m, plain n → S_T T n = false → (m ∈ O n ↔ m ∈ O_T T n).
  Hypothesis Hw : run_word (M := lq_menu O) (menu T) (S_T T) (dinit q) r w.
  Hypothesis Hq : ok q.1.
  Hypothesis HT : ok T.

  Definition aval (a : coact) : Prop :=
    match a with
    | CoIn _ _ v => V v
    | CoMeas _ M qs i => ∃ k' : Out (meas_of M qs), i = code _ k'
    | _ => True
    end.

  Lemma tn_ok n X : Forall aval n → X ∈ tnodes T n → ok X.
  Proof.
    revert X. induction n as [|a n IH] using rev_ind; intros X Hn HX.
    - rewrite tnodes_nil in HX. apply list_elem_of_singleton in HX. by subst.
    - apply Forall_app in Hn as [Hn Ha0]. assert (Ha : aval a) by (by inversion Ha0).
      apply tnodes_app_elem in HX as (X0 & HX0 & HX). pose proof (IH X0 Hn HX0) as Ho.
      pose proof (co_succ_sound _ _ _ HX) as Hs. apply (step_ok X0 _ _ X Ho Hs).
      destruct a as [k c v|k c v|k E qs|k M qs i|k qs]; simpl in Ha |- *; try done.
      destruct Ha as [k' ->]. destruct (step_meas X0 _ _ X Ho Hs M qs _ eq_refl) as (Hm & Hl & Hf).
      by apply HVm.
  Qed.

  Lemma OT_ok n k c v : Forall aval n → (k, c, v) ∈ O_T T n → V v.
  Proof.
    intros Hn (X & HX & Hne)%O_T_spec. destruct (co_succ X (CoOut k c v)) as [|X1 l] eqn:E; [done|].
    assert (HX1 : X1 ∈ co_succ X (CoOut k c v)) by (rewrite E; by left).
    exact (step_out X _ _ X1 (tn_ok n X Hn HX) (co_succ_sound _ _ _ HX1) c v eq_refl).
  Qed.

  Lemma sched_ok ρ P s (Δ : list (proc * St)) : ok P → sched_step ρ P s Δ → ∀ y : proc * St, y ∈ Δ → ok y.1.
  Proof.
    intros Ho Hs y Hy. inversion Hs as [R' Hp|E qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hy. subst y. exact (step_ok _ _ _ _ Ho Hp Logic.I).
    - apply list_elem_of_singleton in Hy. subst y. exact (step_ok _ _ _ _ Ho Hp Logic.I).
    - apply list_elem_of_singleton in Hy. subst y. exact (step_ok _ _ _ _ Ho Hp Logic.I).
    - destruct (zip_elem _ _ _ _ y Hf Hy) as (k & R' & Hp & ->). apply (step_ok _ _ _ _ Ho Hp). simpl.
      destruct (step_meas _ _ _ _ Ho Hp M qs _ eq_refl) as (Hm & Hl & Hfq). by apply HVm.
  Qed.

  Lemma run_pool i x : x ∈ r i → Forall aval x.1.1 ∧ ok x.1.2.1 ∧ plain x.1.1.
  Proof.
    revert x. induction i as [|i IH]; intros x Hx.
    - rewrite (proj1 Hw) in Hx. apply list_elem_of_singleton in Hx. subst x. simpl.
      split; [constructor|]. split; [exact Hq|]. intros k c v Hin. by apply elem_of_nil in Hin.
    - destruct (proj2 Hw i) as [(_ & Δs & HF & Eq)|(_ & Eq)]; [|rewrite Eq in Hx; by apply IH].
      rewrite Eq in Hx. destruct (dsum_elem _ _ _ x HF Hx) as ([c ρ] & Δ & Hc & _ & Hstep & HxΔ). simpl in Hstep.
      destruct (IH (c, ρ) Hc) as (Hn & Ho & Hpl). simpl in Hn, Ho, Hpl.
      destruct Hstep as [(Hns & Hs)|(_ & ->)].
      2:{ apply list_elem_of_singleton in HxΔ. subst x. simpl. done. }
      assert (Hsf : S_T T c.1 = false) by (destruct (S_T T c.1) eqn:Es; [exfalso; apply Hns; exact Es|done]).
      apply cstep_cases in Hs. inversion Hs as [n P C s Δ0 Hss|n P C k d v t P' Hin HkC Hp|n P C k d v t P' HI Hp
                      |n P C k E' qs t HI|n P C k qs t HI|n P C k M qs t HI]; subst; simpl in *.
      + apply list_elem_of_fmap in HxΔ as (y & -> & Hy). simpl.
        split; [done|]. split; [exact (sched_ok ρ P s Δ0 Ho Hss y Hy)|done].
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split; [done|]. split; [|done].
        apply (step_ok P _ _ P' Ho Hp). simpl. apply (OT_ok n k d v Hn). apply (HO n _ Hpl Hsf). exact Hin.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [|constructor]. exact (step_out P _ _ P' Ho Hp d v eq_refl). }
        split; [exact (step_ok P _ _ P' Ho Hp Logic.I)|]. by apply plain_app.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [done|constructor]. }
        split; [done|]. by apply plain_app.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [done|constructor]. }
        split; [done|]. by apply plain_app.
      + apply list_elem_of_fmap in HxΔ as (k' & -> & Hk'). simpl. split.
        { apply Forall_app. split; [done|]. constructor; [by eexists|constructor]. }
        split; [done|]. by apply plain_app.
  Qed.

  Hypothesis HfV : fin V.

  Lemma aval_fin o : fin (λ a, offer_of a = o ∧ aval a).
  Proof.
    destruct o as [k c v|k c|k E qs|k M qs|k qs].
    - apply (fin_mono _ (λ a, a = CoOut k c v)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as -> -> ->.
    - apply (fin_mono _ (λ a, ∃ v, V v ∧ a = CoIn k c v)); [|exact (fin_img (λ v, CoIn k c v) V HfV)].
      intros a [Eo Ha]. destruct a; simpl in Eo; try discriminate Eo. injection Eo as -> ->. by exists v.
    - apply (fin_mono _ (λ a, a = CoOp k E qs)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as -> -> ->.
    - apply (fin_mono _ (λ a, ∃ k' : Out (meas_of M qs), In k' (outs (meas_of M qs)) ∧ a = CoMeas k M qs (code _ k'))).
      + intros a [Eo Ha]. destruct a as [| | |k0 M0 qs0 i|]; simpl in Eo; try discriminate Eo.
        injection Eo as -> -> ->. destruct Ha as [k' ->]. exists k'. split; [apply outs_all|done].
      + apply (fin_img (λ k' : Out (meas_of M qs), CoMeas k M qs (code _ k')) (λ k', In k' (outs (meas_of M qs)))).
        exists (outs (meas_of M qs)). intros x Hx. by apply list_elem_of_In.
    - apply (fin_mono _ (λ a, a = CoInit k qs)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as -> ->.
  Qed.

  Lemma vis_menu m a : visited r (m ++ [a]) → menu T m (offer_of a) ∧ aval a.
  Proof.
    intros (i & [nc cc] & ρ & Hin & Ec). simpl in Ec. subst nc. split.
    - exact (visited_run (M := lq_menu O) (menu T) (S_T T) r w (Hrun0 q O T r w Hw) (Hinit0 q O T r w Hw _)
               i (m ++ [a], cc, ρ) Hin m a [] eq_refl).
    - destruct (run_pool i (m ++ [a], cc, ρ) Hin) as (Hn & _). simpl in Hn.
      apply Forall_app in Hn as [_ Ha]. by inversion Ha.
  Qed.

  Lemma vis_level d : fin (λ n, length n = d ∧ visited r n).
  Proof.
    induction d as [|d IH].
    - apply (fin_mono _ (λ n, n = [])); [|apply fin_eq]. intros n [Hl _]. by destruct n.
    - apply (fin_mono _ (λ n, ∃ m, (length m = d ∧ visited r m)
                           ∧ ∃ o, menu T m o ∧ ∃ a, (offer_of a = o ∧ aval a) ∧ n = m ++ [a])).
      + intros n [Hl Hv]. destruct n as [|a m _] using rev_ind; [discriminate Hl|].
        rewrite length_app in Hl. simpl in Hl. destruct (vis_menu m a Hv) as [Hm Ha].
        exists m. split; [split; [lia|exact (vis_prefix q O T r w Hw m [a] Hv)]|].
        exists (offer_of a). split; [done|]. exists a. done.
      + apply (fin_bind _ _ IH). intros m _. apply (fin_bind _ _ (menu_fin T m)). intros o _.
        exact (fin_img (λ a, m ++ [a]) _ (aval_fin o)).
  Qed.

  Hypothesis HTn : norec T = true.

  Lemma vis_fin : fin (visited r).
  Proof.
    apply (fin_mono _ (λ n, ∃ d, d ∈ seq 0 (Datatypes.S (sz T)) ∧ (length n = d ∧ visited r n))).
    - intros n Hv. exists (length n). split; [|done]. apply elem_of_seq.
      destruct n as [|a m _] using rev_ind; [simpl; lia|].
      pose proof (menu_depth T m _ HTn (proj1 (vis_menu m a Hv))) as Hd. rewrite length_app. simpl. lia.
    - apply (fin_bind _ _ (fin_elem _)). intros d _. apply vis_level.
  Qed.
End Pool.

Definition sup (Φ : (val → Prop) → (meas → Prop) → nat → Prop) : Prop :=
  ∃ (V0 : list val) (ML : list meas) (L : nat), ∀ (V : val → Prop) (MM : meas → Prop) L',
    (∀ v, v ∈ V0 → V v) → (∀ M, M ∈ ML → MM M) → L ≤ L' → Φ V MM L'.

Lemma sup_true : sup (λ _ _ _, True).
Proof. by exists [], [], 0. Qed.

Lemma sup_and Φ Ψ : sup Φ → sup Ψ → sup (λ V MM L, Φ V MM L ∧ Ψ V MM L).
Proof.
  intros (V1 & M1 & L1 & Hs1) (V2 & M2 & L2 & Hs2). exists (V1 ++ V2), (M1 ++ M2), (max L1 L2).
  intros V MM L' HV HM HL. split.
  - apply Hs1; [intros v Hv; apply HV, elem_of_app; by left|intros M Hm; apply HM, elem_of_app; by left|lia].
  - apply Hs2; [intros v Hv; apply HV, elem_of_app; by right|intros M Hm; apply HM, elem_of_app; by right|lia].
Qed.

Lemma sup_mono (Φ Ψ : (val → Prop) → (meas → Prop) → nat → Prop) :
  (∀ V MM L, Φ V MM L → Ψ V MM L) → sup Φ → sup Ψ.
Proof. intros Hi (V0 & ML & L & Hs). exists V0, ML, L. intros V MM L' HV HM HL. by apply Hi, Hs. Qed.

Lemma oke_sup e : sup (λ V _ _, oke V e).
Proof.
  induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2].
  - exact sup_true.
  - exists [w], [], 0. intros V MM L' HV _ _. apply HV. by left.
  - exact IH.
  - exact (sup_and _ _ IH1 IH2).
  - exact (sup_and _ _ IH1 IH2).
  - exact (sup_and _ _ IH1 IH2).
Qed.

Lemma okes_sup es : sup (λ V _ _, Forall (oke V) es).
Proof.
  induction es as [|e es IH].
  - exists [], [], 0. intros V MM L' _ _ _. constructor.
  - refine (sup_mono _ _ _ (sup_and _ _ (oke_sup e) IH)). intros V MM L [Ha Hb]. by constructor.
Qed.

Lemma okpre_sup 𝜆 : sup (λ V MM L, okpre V MM L 𝜆).
Proof.
  destruct 𝜆 as [t|t c|t E es|t M es|t es].
  - exact sup_true.
  - exact sup_true.
  - exact (okes_sup es).
  - assert (HA : sup (λ _ MM _, MM M)).
    { exists [], [M], 0. intros V MM L' _ HM _. apply HM. by left. }
    assert (HB : sup (λ _ _ L, length es ≤ L)).
    { exists [], [], (length es). intros V MM L' _ _ HL. exact HL. }
    exact (sup_and _ _ (okes_sup es) (sup_and _ _ HA HB)).
  - exact (okes_sup es).
Qed.

Lemma ok_sup : (∀ P, sup (λ V MM L, ok V MM L P)) ∧ (∀ g, sup (λ V MM L, gok V MM L g)).
Proof.
  apply proc_guard_ind.
  - intros t c e. exact (oke_sup e).
  - intros e P IHP Q IHQ. exact (sup_and _ _ (oke_sup e) (sup_and _ _ IHP IHQ)).
  - intros P IHP Q IHQ. exact (sup_and _ _ IHP IHQ).
  - intros P IHP. exact IHP.
  - intros X. exact sup_true.
  - intros t X P IHP. exact IHP.
  - intros g IHg. exact IHg.
  - intros es. exact (okes_sup es).
  - exact sup_true.
  - intros 𝜆 P IHP. exact (sup_and _ _ (okpre_sup 𝜆) IHP).
  - intros g1 IH1 g2 IH2. exact (sup_and _ _ IH1 IH2).
Qed.

Definition pool `{QM : QuantumModel} (V0 : list val) (ML : list meas) (L : nat) (v : val) : Prop :=
  v ∈ V0 ∨ (∃ b, v = VBool b)
  ∨ ∃ M qs (k' : Out (meas_of M qs)),
      M ∈ ML ∧ length qs ≤ L ∧ Forall (λ x, VQubit x ∈ V0) qs ∧ v = VNat (code _ k').

Lemma pool_fin `{QM : QuantumModel} V0 ML L : fin (pool V0 ML L).
Proof.
  unfold pool. apply fin_or; [apply fin_elem|]. apply fin_or.
  - apply (fin_mono _ (λ v, v ∈ [VBool true; VBool false])); [|apply fin_elem].
    intros v [[] ->]; [by left|right; by left].
  - apply (fin_mono _ (λ v, ∃ M, M ∈ ML ∧ ∃ qs,
        (∃ n, n ∈ seq 0 (Datatypes.S L) ∧ (length qs = n ∧ Forall (λ x, VQubit x ∈ V0) qs))
        ∧ ∃ k' : Out (meas_of M qs), In k' (outs (meas_of M qs)) ∧ v = VNat (code _ k'))).
    + intros v (M & qs & k' & HM & Hl & Hf & ->). exists M. split; [done|]. exists qs. split.
      * exists (length qs). split; [apply elem_of_seq; lia|done].
      * exists k'. split; [apply outs_all|done].
    + apply (fin_bind _ _ (fin_elem ML)). intros M _. apply fin_bind.
      * apply (fin_bind _ _ (fin_elem _)). intros n _. apply fin_lists.
        exists (omap (λ v, match v with VQubit x => Some x | _ => None end) V0). intros x Hx.
        apply list_elem_of_omap. by exists (VQubit x).
      * intros qs _.
        apply (fin_img (λ k' : Out (meas_of M qs), VNat (code _ k')) (λ k', In k' (outs (meas_of M qs)))).
        exists (outs (meas_of M qs)). intros x Hx. by apply list_elem_of_In.
Qed.

Theorem all_finitary `{QM : QuantumModel} (p q : proc * St) : finitary p q.
Proof.
  intros O Ch K I S r w ((T & HT & HO & -> & -> & _) & _) Hw.
  destruct (proj1 ok_sup q.1) as (V1 & M1 & L1 & Hq1). destruct (proj1 ok_sup T) as (V2 & M2 & L2 & HT2).
  refine (vis_fin (pool (V1 ++ V2) (M1 ++ M2) (max L1 L2)) (λ M, M ∈ M1 ++ M2) (max L1 L2) _ _ q O T r w HO Hw _ _ _ _).
  - intros b. right. left. by exists b.
  - intros M qs k' HM Hl Hf. right. right. exists M, qs, k'. split; [done|]. split; [done|]. split; [|done].
    eapply Forall_impl; [exact Hf|]. intros x [Hx|[(b & Hb)|(M' & qs' & k'' & _ & _ & _ & Hb)]];
      [done|discriminate Hb|discriminate Hb].
  - apply Hq1; [intros v Hv; left; apply elem_of_app; by left|intros M HM; apply elem_of_app; by left|lia].
  - apply HT2; [intros v Hv; left; apply elem_of_app; by right|intros M HM; apply elem_of_app; by right|lia].
  - apply pool_fin.
  - exact (proj1 obs_norec T (proj1 (proj1 (proj1 HT)))).
Qed.

Theorem trace_characterisation_all `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_trace p q).
Proof.
  intros Hz. exact (trace_characterisation DC p q Hz (all_finitary p q)).
Qed.
(* end hide *)
