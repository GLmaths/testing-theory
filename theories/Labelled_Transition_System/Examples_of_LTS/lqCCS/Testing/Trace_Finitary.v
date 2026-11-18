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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Truncation lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Trace_Complete lqCCS.Testing.Trace_Sound lqCCS.Testing.Trace_Convergence.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Trace_Finitary.
  Context `{lqP : lqCCS_Parameters}.

Section Pool.
  Context `{QM : QuantumModel} (V : val → Prop) (MM : meas → Prop) (L : nat).

  Fixpoint oke (e : exp) : Prop :=
    match e with
    | #_ => True
    | EVal v => V v
    | ¬ₑ e => oke e
    | a ∨ₑ b | a ≤ₑ b | a =ₑ b => oke a ∧ oke b
    end.

  Definition okpre (π : prefix) : Prop :=
    match π with
    | _ ∶ 𝛕 | _ ∶ _ ? => True
    | POp _ _ es => Forall oke es
    | PReinit _ e => oke e
    | _ ∶ M ⦅es ▷⦆ => Forall oke es ∧ MM M ∧ length es ≤ L
    end.

  Fixpoint ok (P : prog) : Prop :=
    match P with
    | PSend _ _ e => oke e
    | If e Then P Else Q => oke e ∧ ok P ∧ ok Q
    | P ∥ Q => ok P ∧ ok Q
    | ν P | _ ∶ rec ∙ P => ok P
    | PVar _ => True
    | PG g => gok g
    end
  with gok (g : guard) : Prop :=
    match g with
    | 𝟘{es} => Forall oke es
    | 𝟙 => True
    | π ∙ P => okpre π ∧ ok P
    | (g1 + g2)%lq => gok g1 ∧ gok g2
    end.

  Hypothesis HVb : ∀ b : bool, V b.
  Hypothesis HVm : ∀ M qs n, In n (outs (meas_of M qs)) →
    MM M → length qs ≤ L → Forall (λ x, V $x) qs → V (VNat n).

  Lemma oke_eval e v : oke e → 〚 e 〛 = v → V v.
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

  Lemma oke_subst t v e : V v → oke e → oke (exp_subst t v e).
  Proof.
    intros Hv. induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; try tauto.
    intros _. repeat case_decide; simpl; done.
  Qed.

  Lemma oke_shift j e : oke e → oke (exp_shift j e).
  Proof.
    induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; try tauto.
    intros _. repeat case_decide; simpl; done.
  Qed.

  Lemma okes_subst j v es : V v → Forall oke es → Forall oke (map (exp_subst j v) es).
  Proof. intros Hv Hes. apply Forall_map. eapply Forall_impl; [exact Hes|]. intros e. by apply oke_subst. Qed.

  Lemma okes_shift j es : Forall oke es → Forall oke (map (exp_shift j) es).
  Proof. intros Hes. apply Forall_map. eapply Forall_impl; [exact Hes|]. intros e. by apply oke_shift. Qed.

  Lemma okpre_subst j v π : V v → okpre π → okpre (prefix_subst j v π).
  Proof.
    intros Hv. destruct π as [t|t c|t U es|t M es|t e]; simpl; try done.
    - by apply okes_subst.
    - intros (Ho & Hm & Hl). rewrite length_map. split; [by apply okes_subst|done].
    - by apply oke_subst.
  Qed.

  Lemma okpre_shift j π : okpre π → okpre (prefix_shift j π).
  Proof.
    destruct π as [t|t c|t U es|t M es|t e]; simpl; try done.
    - by apply okes_shift.
    - intros (Ho & Hm & Hl). rewrite length_map. split; [by apply okes_shift|done].
    - by apply oke_shift.
  Qed.

  Lemma ok_subst v : V v → (∀ P j, ok P → ok (P ⁅ v // j ⁆ᵥ)) ∧ (∀ g j, gok g → gok (gsubst j v g)).
  Proof.
    intros Hv. apply prog_guard_ind; simpl.
    - intros t c e j Ho. by apply oke_subst.
    - intros e P IHP Q IHQ j (He & HP & HQ). split; [by apply oke_subst|]. split; auto.
    - intros P IHP Q IHQ j [HP HQ]. split; auto.
    - intros P IHP j HP. auto.
    - done.
    - intros t P IHP j HP. auto.
    - intros g IHg j Hg. auto.
    - intros es j Ho. by apply okes_subst.
    - done.
    - intros π P IHP j [Ha Hb]. split; [by apply okpre_subst|auto].
    - intros g1 IH1 g2 IH2 j [Ha Hb]. split; auto.
  Qed.

  Lemma ok_shiftv : (∀ P j, ok P → ok (shiftv j P)) ∧ (∀ g j, gok g → gok (gshiftv j g)).
  Proof.
    apply prog_guard_ind; simpl.
    - intros t c e j Ho. by apply oke_shift.
    - intros e P IHP Q IHQ j (He & HP & HQ). split; [by apply oke_shift|]. split; auto.
    - intros P IHP Q IHQ j [HP HQ]. split; auto.
    - intros P IHP j HP. auto.
    - done.
    - intros t P IHP j HP. auto.
    - intros g IHg j Hg. auto.
    - intros es j Ho. by apply okes_shift.
    - done.
    - intros π P IHP j [Ha Hb]. split; [by apply okpre_shift|auto].
    - intros g1 IH1 g2 IH2 j [Ha Hb]. split; auto.
  Qed.

  Lemma ok_ren : (∀ P f, ok P → ok (ren f P)) ∧ (∀ g f, gok g → gok (gren f g)).
  Proof.
    apply prog_guard_ind; simpl.
    - intros t c e f Ho. exact Ho.
    - intros e P IHP Q IHQ f (He & HP & HQ). split; [done|]. split; auto.
    - intros P IHP Q IHQ f [HP HQ]. split; auto.
    - intros P IHP f HP. auto.
    - intros X f _. exact Logic.I.
    - intros t P IHP f HP. auto.
    - intros g IHg f Hg. auto.
    - intros es f Ho. exact Ho.
    - intros f _. exact Logic.I.
    - intros π P IHP f [Ha Hb]. split; [by destruct π|auto].
    - intros g1 IH1 g2 IH2 f [Ha Hb]. split; auto.
  Qed.

  Lemma ok_tren : (∀ P f, ok P → ok (tren f P)) ∧ (∀ g f, gok g → gok (gtren f g)).
  Proof.
    apply prog_guard_ind; simpl.
    - intros t c e f Ho. exact Ho.
    - intros e P IHP Q IHQ f (He & HP & HQ). split; [done|]. split; auto.
    - intros P IHP Q IHQ f [HP HQ]. split; auto.
    - intros P IHP f HP. auto.
    - intros X f _. exact Logic.I.
    - intros t P IHP f HP. auto.
    - intros g IHg f Hg. auto.
    - intros es f Ho. exact Ho.
    - intros f _. exact Logic.I.
    - intros π P IHP f [Ha Hb]. split; [by destruct π|auto].
    - intros g1 IH1 g2 IH2 f [Ha Hb]. split; auto.
  Qed.

  Lemma ok_iter n Q : ok Q → ok (Nat.iter n ⇧ᵥ Q).
  Proof. intros HQ. induction n as [|n IH]; simpl; [done|]. by apply (proj1 ok_shiftv). Qed.

  Lemma ok_rshift : (∀ P j, ok P → ok (rshift j P)) ∧ (∀ g j, gok g → gok (grshift j g)).
  Proof.
    apply prog_guard_ind; simpl.
    - intros t c e j Ho. exact Ho.
    - intros e P IHP Q IHQ j (He & HP & HQ). split; [done|]. split; auto.
    - intros P IHP Q IHQ j [HP HQ]. split; auto.
    - intros P IHP j HP. auto.
    - intros i j _. by case_decide.
    - intros t P IHP j HP. auto.
    - intros g IHg j Hg. auto.
    - intros es j Ho. exact Ho.
    - intros j _. exact Logic.I.
    - intros π P IHP j [Ha Hb]. split; [done|auto].
    - intros g1 IH1 g2 IH2 j [Ha Hb]. split; auto.
  Qed.

  Lemma ok_prsubst :
    (∀ P j Q, ok P → ok Q → ok (P ⁅ Q // j ⁆ₚ)) ∧ (∀ g j Q, gok g → ok Q → gok (gpr_subst j g Q)).
  Proof.
    apply prog_guard_ind; simpl.
    - intros t c e j R Ho _. exact Ho.
    - intros e P IHP Q IHQ j R (He & HP & HQ) HR. split; [done|]. split; auto.
    - intros P IHP Q IHQ j R [HP HQ] HR. split; auto.
    - intros P IHP j R HP HR. apply IHP; [done|]. by apply (proj1 ok_ren).
    - intros Y j R _ HR. by repeat case_decide.
    - intros t P IHP j R HP HR. apply IHP; [done|]. by apply (proj1 ok_rshift).
    - intros g IHg j R Hg HR. auto.
    - intros es j R Ho _. exact Ho.
    - intros j R _ _. exact Logic.I.
    - intros π P IHP j R [Ha Hb] HR. split; [done|]. apply IHP; [done|]. by apply ok_iter.
    - intros g1 IH1 g2 IH2 j R [Ha Hb] HR. split; auto.
  Qed.

  Definition lok (𝜆 : Labels prog_action) : Prop :=
    match 𝜆 with
    | _ ? v => V v
    | _ ⦅_⦆? n => V (VNat n)
    | _ => True
    end.

  Definition mq (M : meas) (qs : list qubit) : Prop :=
    MM M ∧ length qs ≤ L ∧ Forall (λ x, V $x) qs.

  Lemma evq es qs : Forall oke es → eval_qubits es = Some qs →
    length qs = length es ∧ Forall (λ x, V $x) qs.
  Proof.
    intros Ho He. apply mapM_Some in He. induction He as [|e x es qs Hex _ IH]; [by split|].
    apply Forall_cons in Ho as [Ho1 Ho2]. destruct (IH Ho2) as [Hl Hf]. split; [simpl; by rewrite Hl|].
    constructor; [|done]. unfold eval_qubit in Hex. destruct (eval e) as [[b|n|x0]|] eqn:Ee; try discriminate Hex.
    injection Hex as <-. exact (oke_eval e _ Ho1 Ee).
  Qed.

  Lemma gstep_noout g k c v P' : g ↛ᵍ{c ! v}[k] P'.
  Proof.
    intros Hs. remember (c ! v) as 𝜆 eqn:El. induction Hs; try discriminate El; auto.
  Qed.

  Lemma step_out P k 𝜆 P' : ok P → P ⟶ₚ{𝜆}[k] P' → ∀ c v, 𝜆 = c ! v → V v.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [g k 𝜆 P' Hg|t c e v He|e P Q k 𝜆 P' He Hs IH|e P Q k 𝜆 Q' He Hs IH
      |P Q k 𝜆 P' Hs IH|P Q k 𝜆 Q' Hs IH|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
      |P k 𝜆 P' Hs IH|t P]; simpl; intros Ho c0 v0 El.
    - subst 𝜆. exfalso. exact (gstep_noout _ _ _ _ _ Hg).
    - injection El as _ <-. exact (oke_eval e v Ho He).
    - exact (IH (proj1 (proj2 Ho)) c0 v0 El).
    - exact (IH (proj2 (proj2 Ho)) c0 v0 El).
    - exact (IH (proj1 Ho) c0 v0 El).
    - exact (IH (proj2 Ho) c0 v0 El).
    - discriminate El.
    - discriminate El.
    - subst 𝜆. exact (IH Ho _ v0 eq_refl).
    - discriminate El.
  Qed.

  Lemma gstep_meas g k 𝜆 P' : gok g → g ⟶ᵍ{𝜆}[k] P' → ∀ M qs n, 𝜆 = M ⦅qs⦆? n → mq M qs.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [t P|t c v P|t U es qs P He|t M es qs n P He|t es qs P He
      |g1 g2 k 𝜆 P' Hs IH|g1 g2 k 𝜆 P' Hs IH]; simpl; intros Ho M0 qs0 n0 El; try discriminate El.
    - injection El as <- <- <-. destruct Ho as [(Hes & Hm & Hl) _]. destruct (evq es qs Hes He) as [Hlen Hf].
      split; [done|]. split; [lia|done].
    - exact (IH (proj1 Ho) M0 qs0 n0 El).
    - exact (IH (proj2 Ho) M0 qs0 n0 El).
  Qed.

  Lemma step_meas P k 𝜆 P' : ok P → P ⟶ₚ{𝜆}[k] P' → ∀ M qs n, 𝜆 = M ⦅qs⦆? n → mq M qs.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [g k 𝜆 P' Hg|t c e v He|e P Q k 𝜆 P' He Hs IH|e P Q k 𝜆 Q' He Hs IH
      |P Q k 𝜆 P' Hs IH|P Q k 𝜆 Q' Hs IH|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
      |P k 𝜆 P' Hs IH|t P]; simpl; intros Ho M0 qs0 n0 El; try discriminate El.
    - exact (gstep_meas g k 𝜆 P' Ho Hg M0 qs0 n0 El).
    - exact (IH (proj1 (proj2 Ho)) M0 qs0 n0 El).
    - exact (IH (proj2 (proj2 Ho)) M0 qs0 n0 El).
    - exact (IH (proj1 Ho) M0 qs0 n0 El).
    - exact (IH (proj2 Ho) M0 qs0 n0 El).
    - subst 𝜆. exact (IH Ho M0 qs0 n0 eq_refl).
  Qed.

  Lemma gstep_ok g k 𝜆 P' : gok g → g ⟶ᵍ{𝜆}[k] P' → lok 𝜆 → ok P'.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [t P|t c v P|t U es qs P He|t M es qs n P He|t es qs P He
      |g1 g2 k 𝜆 P' Hs IH|g1 g2 k 𝜆 P' Hs IH]; simpl; intros Ho Hl.
    - exact (proj2 Ho).
    - exact (proj1 (ok_subst v Hl) P 0 (proj2 Ho)).
    - exact (proj2 Ho).
    - exact (proj1 (ok_subst (VNat n) Hl) P 0 (proj2 Ho)).
    - exact (proj2 Ho).
    - exact (IH (proj1 Ho) Hl).
    - exact (IH (proj2 Ho) Hl).
  Qed.

  Lemma lok_ren 𝜆 : lok (ren_lbl Datatypes.S 𝜆) ↔ lok 𝜆.
  Proof. destruct 𝜆 as [[]|]; done. Qed.

  Lemma step_ok P k 𝜆 P' : ok P → P ⟶ₚ{𝜆}[k] P' → lok 𝜆 → ok P'.
  Proof.
    intros Ho Hs. revert Ho. induction Hs as [g k 𝜆 P' Hg|t c e v He|e P Q k 𝜆 P' He Hs IH|e P Q k 𝜆 Q' He Hs IH
      |P Q k 𝜆 P' Hs IH|P Q k 𝜆 Q' Hs IH|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2|P Q t t' c v P' Q' Hs1 IH1 Hs2 IH2
      |P k 𝜆 P' Hs IH|t P]; simpl; intros Ho Hl.
    - exact (gstep_ok g k 𝜆 P' Ho Hg Hl).
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
    - apply (proj1 ok_prsubst); [done|]. exact (proj1 ok_tren (t ∶ rec ∙ P) tag_up Ho).
  Qed.

  Context (q : prog * St) (O : node → list msg) (T : prog) (r : nat → dist comp) (w : nat → item).
  Hypothesis HO : ∀ z m, plain z → S_T T z = false → (m ∈ O z ↔ m ∈ O_T T z).
  Hypothesis Hw : run_word (M := lq_menu O) (menu T) (S_T T) (dinit q) r w.
  Hypothesis Hq : ok q.1.
  Hypothesis HT : ok T.

  Definition aval (a : coact) : Prop :=
    match a with
    | CoIn _ _ v => V v
    | CoMeas _ M qs n => In n (outs (meas_of M qs))
    | _ => True
    end.

  Lemma tn_ok z X : Forall aval z → X ∈ tnodes T z → ok X.
  Proof.
    revert X. induction z as [|a z IH] using rev_ind; intros X Hn HX.
    - rewrite tnodes_nil in HX. apply list_elem_of_singleton in HX. by subst.
    - apply Forall_app in Hn as [Hn Ha0]. assert (Ha : aval a) by (by inversion Ha0).
      apply tnodes_app_elem in HX as (X0 & HX0 & HX). pose proof (IH X0 Hn HX0) as Ho.
      pose proof (co_succ_step _ _ _ HX) as Hs.
      apply (step_ok X0 _ _ X Ho Hs).
      destruct a as [t c v|t c v|t U qs|t M qs n|t q0|t]; simpl in Ha |- *; try done.
      destruct (step_meas X0 _ _ X Ho Hs M qs _ eq_refl) as (Hm & Hl & Hf).
      by apply (HVm M qs n).
  Qed.

  Lemma OT_ok z t c v : Forall aval z → (t, c, v) ∈ O_T T z → V v.
  Proof.
    intros Hn (X & HX & Hne)%O_T_spec. destruct (co_succ X (CoOut t c v)) as [|X1 l] eqn:E; [done|].
    assert (HX1 : X1 ∈ co_succ X (CoOut t c v)) by (rewrite E; by left).
    pose proof (co_succ_step _ _ _ HX1) as Hs.
    exact (step_out X _ _ X1 (tn_ok z X Hn HX) Hs c v eq_refl).
  Qed.

  Lemma sched_ok ρ P k (Δ : list (prog * St)) : ok P → sched_step ρ P k Δ → ∀ y : prog * St, y ∈ Δ → ok y.1.
  Proof.
    intros Ho Hs y Hy. inversion Hs as [R' Hp|U qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 Hf]; subst.
    - apply list_elem_of_singleton in Hy. subst y. exact (step_ok _ _ _ _ Ho Hp Logic.I).
    - apply list_elem_of_singleton in Hy. subst y. exact (step_ok _ _ _ _ Ho Hp Logic.I).
    - apply list_elem_of_singleton in Hy. subst y. exact (step_ok _ _ _ _ Ho Hp Logic.I).
    - destruct (zip_elem _ _ _ _ y Hf Hy) as (t & R' & Hk & Hp & ->). apply (step_ok _ _ _ _ Ho Hp). simpl.
      destruct (step_meas _ _ _ _ Ho Hp M qs _ eq_refl) as (Hm & Hl & Hfq).
      apply (HVm M qs t); [|done..]. apply list_elem_of_In. by apply outs_nz_spec in Hk as [? _].
  Qed.

  Lemma run_pool n x : x ∈ r n → Forall aval x.1.1 ∧ ok x.1.2.1 ∧ plain x.1.1.
  Proof.
    revert x. induction n as [|n IH]; intros x Hx.
    - rewrite (proj1 Hw) in Hx. apply list_elem_of_singleton in Hx. subst x. simpl.
      split; [constructor|]. split; [exact Hq|]. intros t c v Hin. by apply elem_of_nil in Hin.
    - destruct (proj2 Hw n) as [(_ & Δs & HF & Eq)|(_ & Eq)]; [|rewrite Eq in Hx; by apply IH].
      rewrite Eq in Hx. destruct (dsum_elem _ _ _ x HF Hx) as ([c ρ] & Δ & Hc & _ & Hstep & HxΔ). simpl in Hstep.
      destruct (IH (c, ρ) Hc) as (Hn & Ho & Hpl). simpl in Hn, Ho, Hpl.
      destruct Hstep as [(Hns & Hs)|(_ & ->)].
      2:{ apply list_elem_of_singleton in HxΔ. subst x. simpl. done. }
      assert (Hsf : S_T T c.1 = false) by (destruct (S_T T c.1) eqn:Es; [exfalso; apply Hns; exact Es|done]).
      apply cstep_cases in Hs. inversion Hs as [z P C k Δ0 Hss|z P C t d v t' P' Hin HkC Hp|z P C t d v t' P' HI Hp
                      |z P C t U' qs t' HI|z P C t q0 t' HI|z P C t M qs t' HI|z P C t t' HI]; subst; simpl in *.
      + apply list_elem_of_fmap in HxΔ as (y & -> & Hy). simpl.
        split; [done|]. split; [exact (sched_ok ρ P k Δ0 Ho Hss y Hy)|done].
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split; [done|]. split; [|done].
        apply (step_ok P _ _ P' Ho Hp). simpl. apply (OT_ok z t d v Hn). apply (HO z _ Hpl Hsf). exact Hin.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [|constructor]. exact (step_out P _ _ P' Ho Hp d v eq_refl). }
        split; [exact (step_ok P _ _ P' Ho Hp Logic.I)|]. by apply plain_app.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [done|constructor]. }
        split; [done|]. by apply plain_app.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [done|constructor]. }
        split; [done|]. by apply plain_app.
      + apply list_elem_of_fmap in HxΔ as (n' & -> & Hk'). simpl. split.
        { apply Forall_app. split; [done|]. constructor; [apply list_elem_of_In; by apply outs_nz_spec in Hk' as [? _]|constructor]. }
        split; [done|]. by apply plain_app.
      + apply list_elem_of_singleton in HxΔ. subst x. simpl. split.
        { apply Forall_app. split; [done|]. constructor; [done|constructor]. }
        split; [done|]. by apply plain_app.
  Qed.

  Hypothesis HfV : fin V.

  Lemma aval_fin o : fin (λ a, offer_of a = o ∧ aval a).
  Proof.
    destruct o as [t c v|t c|t U qs|t M qs|t q0|t].
    - apply (fin_mono _ (λ a, a = CoOut t c v)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as -> -> ->.
    - apply (fin_mono _ (λ a, ∃ v, V v ∧ a = CoIn t c v)); [|exact (fin_img (λ v, CoIn t c v) V HfV)].
      intros a [Eo Ha]. destruct a; simpl in Eo; try discriminate Eo. injection Eo as -> ->. by exists v.
    - apply (fin_mono _ (λ a, a = CoOp t U qs)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as -> -> ->.
    - apply (fin_mono _ (λ a, ∃ n : nat, In n (outs (meas_of M qs)) ∧ a = CoMeas t M qs n)).
      + intros a [Eo Ha]. destruct a as [| | |t0 M0 qs0 n| |]; simpl in Eo; try discriminate Eo.
        injection Eo as -> -> ->. by exists n.
      + apply (fin_img (λ n : nat, CoMeas t M qs n) (λ n, In n (outs (meas_of M qs)))).
        exists (outs (meas_of M qs)). intros x Hx. by apply list_elem_of_In.
    - apply (fin_mono _ (λ a, a = CoInit t q0)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as -> ->.
    - apply (fin_mono _ (λ a, a = CoUnfold t)); [|apply fin_eq]. intros a [Eo _].
      destruct a; simpl in Eo; try discriminate Eo. by injection Eo as ->.
  Qed.

  Lemma vis_menu z' a : visited r (z' ++ [a]) → menu T z' (offer_of a) ∧ aval a.
  Proof.
    intros (n & [nc cc] & ρ & Hin & Ec). simpl in Ec. subst nc. split.
    - exact (visited_run (M := lq_menu O) (menu T) (S_T T) r w (Hrun0 q O T r w Hw) (Hinit0 q O T r w Hw _)
               n (z' ++ [a], cc, ρ) Hin z' a [] eq_refl).
    - destruct (run_pool n (z' ++ [a], cc, ρ) Hin) as (Hn & _). simpl in Hn.
      apply Forall_app in Hn as [_ Ha]. by inversion Ha.
  Qed.

  Lemma vis_level d : fin (λ z, length z = d ∧ visited r z).
  Proof.
    induction d as [|d IH].
    - apply (fin_mono _ (λ z, z = [])); [|apply fin_eq]. intros z [Hl _]. by destruct z.
    - apply (fin_mono _ (λ z, ∃ z', (length z' = d ∧ visited r z')
                           ∧ ∃ o, menu T z' o ∧ ∃ a, (offer_of a = o ∧ aval a) ∧ z = z' ++ [a])).
      + intros z [Hl Hv]. destruct z as [|a z' _] using rev_ind; [discriminate Hl|].
        rewrite length_app in Hl. simpl in Hl. destruct (vis_menu z' a Hv) as [Hm Ha].
        exists z'. split; [split; [lia|exact (vis_prefix q O T r w Hw z' [a] Hv)]|].
        exists (offer_of a). split; [done|]. exists a. done.
      + apply (fin_bind _ _ IH). intros z' _. apply (fin_bind _ _ (menu_fin T z')). intros o _.
        exact (fin_img (λ a, z' ++ [a]) _ (aval_fin o)).
  Qed.

  Hypothesis HTn : norec T = true.

  Lemma vis_fin : fin (visited r).
  Proof.
    apply (fin_mono _ (λ z, ∃ d, d ∈ seq 0 (Datatypes.S (sz T)) ∧ (length z = d ∧ visited r z))).
    - intros z Hv. exists (length z). split; [|done]. apply elem_of_seq.
      destruct z as [|a z' _] using rev_ind; [simpl; lia|].
      pose proof (menu_depth T z' _ HTn (proj1 (vis_menu z' a Hv))) as Hd. rewrite length_app. simpl. lia.
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

Lemma okpre_sup π : sup (λ V MM L, okpre V MM L π).
Proof.
  destruct π as [t|t c|t U es|t M es|t e].
  - exact sup_true.
  - exact sup_true.
  - exact (okes_sup es).
  - assert (HA : sup (λ _ MM _, MM M)).
    { exists [], [M], 0. intros V MM L' _ HM _. apply HM. by left. }
    assert (HB : sup (λ _ _ L, length es ≤ L)).
    { exists [], [], (length es). intros V MM L' _ _ HL. exact HL. }
    exact (sup_and _ _ (okes_sup es) (sup_and _ _ HA HB)).
  - exact (oke_sup e).
Qed.

Lemma ok_sup : (∀ P, sup (λ V MM L, ok V MM L P)) ∧ (∀ g, sup (λ V MM L, gok V MM L g)).
Proof.
  apply prog_guard_ind.
  - intros t c e. exact (oke_sup e).
  - intros e P IHP Q IHQ. exact (sup_and _ _ (oke_sup e) (sup_and _ _ IHP IHQ)).
  - intros P IHP Q IHQ. exact (sup_and _ _ IHP IHQ).
  - intros P IHP. exact IHP.
  - intros X. exact sup_true.
  - intros t P IHP. exact IHP.
  - intros g IHg. exact IHg.
  - intros es. exact (okes_sup es).
  - exact sup_true.
  - intros π P IHP. exact (sup_and _ _ (okpre_sup π) IHP).
  - intros g1 IH1 g2 IH2. exact (sup_and _ _ IH1 IH2).
Qed.

Definition pool `{QM : QuantumModel} (V0 : list val) (ML : list meas) (L : nat) (v : val) : Prop :=
  v ∈ V0 ∨ (∃ b : bool, v = b)
  ∨ ∃ M qs n, In n (outs (meas_of M qs)) ∧
      M ∈ ML ∧ length qs ≤ L ∧ Forall (λ x, $x ∈ V0) qs ∧ v = VNat n.

Lemma pool_fin `{QM : QuantumModel} V0 ML L : fin (pool V0 ML L).
Proof.
  unfold pool. apply fin_or; [apply fin_elem|]. apply fin_or.
  - apply (fin_mono _ (λ v, v ∈ [VBool true; VBool false])); [|apply fin_elem].
    intros v [[] ->]; [by left|right; by left].
  - apply (fin_mono _ (λ v, ∃ M, M ∈ ML ∧ ∃ qs,
        (∃ n, n ∈ seq 0 (Datatypes.S L) ∧ (length qs = n ∧ Forall (λ x, $x ∈ V0) qs))
        ∧ ∃ n : nat, In n (outs (meas_of M qs)) ∧ v = VNat n)).
    + intros v (M & qs & n & Hk & HM & Hl & Hf & ->). exists M. split; [done|]. exists qs. split.
      * exists (length qs). split; [apply elem_of_seq; lia|done].
      * by exists n.
    + apply (fin_bind _ _ (fin_elem ML)). intros M _. apply fin_bind.
      * apply (fin_bind _ _ (fin_elem _)). intros n _. apply fin_lists.
        exists (omap (λ v, match v with $x => Some x | _ => None end) V0). intros x Hx.
        apply list_elem_of_omap. by exists ($x).
      * intros qs _.
        apply (fin_img (λ n : nat, VNat n) (λ n, In n (outs (meas_of M qs)))).
        exists (outs (meas_of M qs)). intros x Hx. by apply list_elem_of_In.
Qed.

Theorem all_finitary `{QM : QuantumModel} (p q : prog * St) : finitary p q.
Proof.
  intros O Ch K I S r w ((T & HT & HO & -> & -> & _) & _) Hw.
  destruct (proj1 ok_sup q.1) as (V1 & M1 & L1 & Hq1). destruct (proj1 ok_sup T) as (V2 & M2 & L2 & HT2).
  refine (vis_fin (pool (V1 ++ V2) (M1 ++ M2) (max L1 L2)) (λ M, M ∈ M1 ++ M2) (max L1 L2) _ _ q O T r w HO Hw _ _ _ _).
  - intros b. right. left. by exists b.
  - intros M qs n Hk HM Hl Hf. right. right. exists M, qs, n. split_and!; [done|done|done| |done].
    eapply Forall_impl; [exact Hf|]. intros x [Hx|[(b & Hb)|(M' & qs' & n' & _ & _ & _ & _ & Hb)]];
      [done|discriminate Hb|discriminate Hb].
  - apply Hq1; [intros v Hv; left; apply elem_of_app; by left|intros M HM; apply elem_of_app; by left|lia].
  - apply HT2; [intros v Hv; left; apply elem_of_app; by right|intros M HM; apply elem_of_app; by right|lia].
  - apply pool_fin.
  - exact (proj1 obs_norec T (proj1 (proj1 (proj1 HT)))).
Qed.

Theorem trace_characterisation_all `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_trace p q).
Proof.
  intros Hz. exact (trace_characterisation DC p q Hz (all_finitary p q)).
Qed.

End Trace_Finitary.

(* end hide *)
