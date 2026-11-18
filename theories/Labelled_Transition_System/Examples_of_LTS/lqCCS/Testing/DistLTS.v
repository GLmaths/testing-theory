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
(* * lqCCS: the LTS 𝔻 of distributions of components with their co-trace

    The alternative preorder is stated on the LTS [𝔻] whose states are
    distributions of components [(z, (P, C))] weighted by a memory [ρ]:
    [z], the node, is the co-trace the component has performed with the
    observer (the co-actions, with the tag of the observer and the value or
    the outcome), and [C] the outputs the program has consumed (tag,
    channel, value), among the outputs [O z] the observer offers at that
    node.  Outputs are asynchronous: the observer does not
    see when they are consumed, so a consumption does not extend the node;
    it is a silent step of the component, [C] only prevents a second
    consumption.  The labels of [𝔻] are the choices [k] of the program (a
    silent step of every component that has it, as in [Scheduled.v], or the
    consumption of an offered output by the pair of the tags) and the
    instructions [(t, t')], "the tag [t] of the observer, answered by the tag
    [t'] of the program": at every node whose menu offers an input or an
    action on the memory tagged [t], an input is served by an output of the
    program, an operation on the memory is done; the components that are not
    concerned stay.  Three parameters describe the shape of a deterministic
    observer: its menu [I z o] (the inputs and actions on the memory it
    offers at the node [z]), its outputs [O z] at the node [z], and its
    success nodes [S z], closed under extension; the successful components
    are frozen.

    The alternative preorder [≼] is the Smyth comparison of [pMust_smyth]
    in [𝔻], for every shape [(I, O, S)]: the quantification over observers
    is replaced by a quantification over shapes, and the runs of [𝔻] are
    the trees of runs of the configuration LTS following one word of choices. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.Sync_Testing.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Offers of the observer, co-actions, nodes, items *)

Section DistLTS.
  Context `{lqP : lqCCS_Parameters}.

Inductive offer : Type :=
| OffOut (t : tag) (c : channel) (v : val)
| OffIn (t : tag) (c : channel)
| OffOp (t : tag) (U : unitary) (qs : list qubit)
| OffMeas (t : tag) (M : meas) (qs : list qubit)
| OffInit (t : tag) (q : qubit)
| OffUnfold (t : tag).

Inductive coact : Type :=
| CoOut (t : tag) (c : channel) (v : val)
| CoIn (t : tag) (c : channel) (v : val)
| CoOp (t : tag) (U : unitary) (qs : list qubit)
| CoMeas (t : tag) (M : meas) (qs : list qubit) (n : nat)
| CoInit (t : tag) (q : qubit)
| CoUnfold (t : tag).

Definition co_tag (a : coact) : tag :=
  match a with
  | CoOut t _ _ | CoIn t _ _ | CoOp t _ _ | CoMeas t _ _ _ | CoInit t _ | CoUnfold t => t
  end.

(* The action of the observer: it outputs what the program inputs; unfolding is silent. *)
Definition co_act (a : coact) : Labels prog_action :=
  match a with
  | CoOut _ c v => c ! v
  | CoIn _ c v => c ? v
  | CoOp _ U qs => ⦅qs⦆ ! U
  | CoMeas _ M qs n => M ⦅qs⦆? n
  | CoInit _ q => reinit q
  | CoUnfold _ => τ
  end.

Definition node : Type := list coact.

Inductive item : Type :=
| ICh (k : choice)
| IOff (t : tag) (t' : tag).

Definition ext_closed (S : node → bool) : Prop := ∀ z a, S z = true → S (z ++ [a]) = true.

(* A message of the observer: its tag, the channel, the value. *)
Definition msg : Type := tag * channel * val.

Definition co_of_msg (m : msg) : coact := CoOut m.1.1 m.1.2 m.2.

Section Dist.
  Context `{QM : QuantumModel}.
  Context (I : node → offer → Prop) (O : node → list msg) (S : node → bool).

  Notation comp := (node * (prog * list msg))%type.

  (* ** The step of one component *)

  Definition dual (𝜆 : Labels (mem_action + prog_action)) (μ2 : prog_action) : Prop :=
    match 𝜆 with ActExt μ1 => sync_sys μ1 μ2 | τ => False end.

  Definition blocking_offer (o : offer) : Prop :=
    match o with OffOut _ _ _ => False | _ => True end.

  Definition off_tag (o : offer) : tag :=
    match o with
    | OffOut t _ _ | OffIn t _ | OffOp t _ _ | OffMeas t _ _ | OffInit t _ | OffUnfold t => t
    end.

  Definition co_of (o : offer) (𝜆 : Labels (mem_action + prog_action)) : coact :=
    match o with
    | OffOut t c v => CoOut t c v
    | OffIn t c => CoIn t c (match 𝜆 with ActExt (inr (PrOut _ v)) => v | _ => VNat 0 end)
    | OffOp t U qs => CoOp t U qs
    | OffMeas t M qs => CoMeas t M qs (match 𝜆 with ActExt (inl (_ !ₘ n)) => n | _ => 0 end)
    | OffInit t q => CoInit t q
    | OffUnfold t => CoUnfold t
    end.

  Definition answers (o : offer) (𝜆 : Labels (mem_action + prog_action)) : Prop :=
    blocking_offer o ∧ match co_act (co_of o 𝜆) with ActExt μ => dual 𝜆 μ | τ => False end.

  Definition by_tag (k : choice) (t' : tag) : Prop := k = ∅ ∨ k = {[+ t' +]}.

  Inductive cstep (ρ : St) : comp → item → dist comp → Prop :=
  | cs_ch z P C k Δ :
      sched_step ρ P k Δ →
      cstep ρ (z, (P, C)) (ICh k) (map (λ Pρ, ((z, (Pρ.1, C)), Pρ.2)) Δ)
  | cs_recv z P C t c v t' P' :
      (t, c, v) ∈ O z → t ∉ (λ m : msg, m.1.1) <$> C →
      P ⟶ₚ{c ? v}[{[+ t' +]}] P' →
      cstep ρ (z, (P, C)) (ICh {[+ t'; t +]}) [((z, (P', C ++ [(t, c, v)])), ρ)]
  | cs_dual z P C o 𝜆 t' k Λ :
      I z o → vis_step ρ P k 𝜆 Λ → by_tag k t' → answers o 𝜆 →
      cstep ρ (z, (P, C)) (IOff (off_tag o) t')
        (map (λ x, ((z ++ [co_of o x.1], (x.2.1, C)), x.2.2)) Λ)
  | cs_unfold z P C t t' :
      I z (OffUnfold t) →
      cstep ρ (z, (P, C)) (IOff t t') [((z ++ [CoUnfold t], (P, C)), ρ)].

  Lemma cs_in ρ z P C t c v t' P' :
    I z (OffIn t c) → P ⟶ₚ{c ! v}[{[+ t' +]}] P' →
    cstep ρ (z, (P, C)) (IOff t t')
      [((z ++ [CoIn t c v], (P', C)), ρ)].
  Proof.
    intros HI Hp.
    apply (cs_dual ρ z P C (OffIn t c) (ActExt (plbl (PrOut c v))) t' {[+ t' +]} [(ActExt (plbl (PrOut c v)), (P', ρ))] HI).
    - by apply vs_prog.
    - by right.
    - split; [done|]. apply sync_sys_chan. constructor.
  Qed.

  Lemma cs_op ρ z P C t U' qs t' :
    I z (OffOp t U' qs) →
    cstep ρ (z, (P, C)) (IOff t t')
      [((z ++ [CoOp t U' qs], (P, C)), sop_apply U' qs ρ)].
  Proof.
    intros HI.
    apply (cs_dual ρ z P C (OffOp t U' qs) (ActExt (mlbl (? (sop_act U' qs)))) t' ∅
             [(ActExt (mlbl (? (sop_act U' qs))), (P, sop_apply U' qs ρ))] HI).
    - apply vs_sop.
    - by left.
    - split; [done|]. apply sync_sys_mem. constructor.
  Qed.

  Lemma cs_init ρ z P C t q t' :
    I z (OffInit t q) →
    cstep ρ (z, (P, C)) (IOff t t')
      [((z ++ [CoInit t q], (P, C)), init_apply q ρ)].
  Proof.
    intros HI.
    apply (cs_dual ρ z P C (OffInit t q) (ActExt (mlbl (? (init_act q)))) t' ∅
             [(ActExt (mlbl (? (init_act q))), (P, init_apply q ρ))] HI).
    - apply vs_sop.
    - by left.
    - split; [done|]. apply sync_sys_mem. constructor.
  Qed.

  Lemma cs_meas ρ z P C t M qs t' :
    I z (OffMeas t M qs) →
    cstep ρ (z, (P, C)) (IOff t t')
      (map (λ n, ((z ++ [CoMeas t M qs n], (P, C)),
                   M ⦅qs⦆[n] · ρ))
         (outs_nz (meas_of M qs) ρ)).
  Proof.
    intros HI.
    pose proof (cs_dual ρ z P C (OffMeas t M qs) (ActExt (mlbl (meas_of M qs !ₘ 0))) t' ∅ _ HI
                  (vs_meas ρ P (meas_of M qs))) as Hd.
    rewrite map_map in Hd. apply Hd.
    - by left.
    - split; [done|]. apply sync_sys_mem. constructor.
  Qed.

  Inductive cstep_view (ρ : St) : comp → item → dist comp → Prop :=
  | cv_ch z P C k Δ :
      sched_step ρ P k Δ →
      cstep_view ρ (z, (P, C)) (ICh k) (map (λ Pρ, ((z, (Pρ.1, C)), Pρ.2)) Δ)
  | cv_recv z P C t c v t' P' :
      (t, c, v) ∈ O z → t ∉ (λ m : msg, m.1.1) <$> C →
      P ⟶ₚ{c ? v}[{[+ t' +]}] P' →
      cstep_view ρ (z, (P, C)) (ICh {[+ t'; t +]}) [((z, (P', C ++ [(t, c, v)])), ρ)]
  | cv_in z P C t c v t' P' :
      I z (OffIn t c) → P ⟶ₚ{c ! v}[{[+ t' +]}] P' →
      cstep_view ρ (z, (P, C)) (IOff t t')
        [((z ++ [CoIn t c v], (P', C)), ρ)]
  | cv_op z P C t U' qs t' :
      I z (OffOp t U' qs) →
      cstep_view ρ (z, (P, C)) (IOff t t')
        [((z ++ [CoOp t U' qs], (P, C)), sop_apply U' qs ρ)]
  | cv_init z P C t q t' :
      I z (OffInit t q) →
      cstep_view ρ (z, (P, C)) (IOff t t')
        [((z ++ [CoInit t q], (P, C)), init_apply q ρ)]
  | cv_meas z P C t M qs t' :
      I z (OffMeas t M qs) →
      cstep_view ρ (z, (P, C)) (IOff t t')
        (map (λ n, ((z ++ [CoMeas t M qs n], (P, C)),
                     M ⦅qs⦆[n] · ρ))
           (outs_nz (meas_of M qs) ρ))
  | cv_unfold z P C t t' :
      I z (OffUnfold t) →
      cstep_view ρ (z, (P, C)) (IOff t t') [((z ++ [CoUnfold t], (P, C)), ρ)].

  Lemma cstep_cases ρ c it Δ : cstep ρ c it Δ → cstep_view ρ c it Δ.
  Proof.
    intros Hc. destruct Hc as [z P C k Δ Hs|z P C t c v t' P' HE HC Hp|z P C o 𝜆 t' k Λ HI Hv Ht [Hb Hd]|z P C t t' HI].
    - by apply cv_ch.
    - by apply cv_recv.
    - destruct Hv as [t0 μ P' Hp|ℰ|M qs].
      + destruct Ht as [Ht|Ht]; [by apply choice_tag_neq_eps in Ht|]. apply choice_tag_inj in Ht as ->.
        destruct o as [t c v|t c|t U' qs|t M qs|t q|t]; simpl in *; try done.
        * inversion Hd as [|? ? Hsc]; subst. destruct μ; inversion Hsc; subst. by apply cv_in.
        * inversion Hd as [|? ? Hsc]; subst. inversion Hsc.
        * inversion Hd as [|? ? Hsc]; subst. inversion Hsc.
        * inversion Hd as [|? ? Hsc]; subst. inversion Hsc.
      + destruct o as [t c v|t c|t U' qs|t M qs|t q|t]; simpl in *; try done.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy; subst. by apply cv_op.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy; subst. by apply cv_init.
      + destruct o as [t c v|t c|t U' qs'|t M' qs'|t q'|t]; simpl in *; try done.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy; subst. rewrite map_map. simpl. by apply cv_meas.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
    - by apply cv_unfold.
  Qed.

  #[global] Instance dlts : SchedSts comp item :=
    {| pMust_scheduled.sstep := cstep; psuccess := λ x, S x.1 = true |}.

  Lemma cstep_nonzero ρ c it Θ :
    ρ ≠ szero → cstep ρ c it Θ → ∀ x, x ∈ Θ → x.2 ≠ szero.
  Proof.
    intros Hρ Hc x Hx. apply cstep_cases in Hc. inversion Hc as [? ? ? k Δ Hs| | | | |? ? ? t M qs t' HI|]; subst.
    - apply list_elem_of_fmap in Hx as (Pρ & -> & HPρ). destruct Pρ as [P' ρ'].
      exact (sched_step_nonzero ρ _ _ _ Hρ Hs P' ρ' HPρ).
    - apply list_elem_of_singleton in Hx. by subst x.
    - apply list_elem_of_singleton in Hx. by subst x.
    - apply list_elem_of_singleton in Hx. subst x. by apply sop_apply_nonzero.
    - apply list_elem_of_singleton in Hx. subst x. by apply init_apply_nonzero.
    - apply list_elem_of_fmap in Hx as (n & -> & Hk'). by apply outs_nz_spec in Hk' as [_ ?].
    - apply list_elem_of_singleton in Hx. by subst x.
  Qed.

  (* The initial distribution: one component at the empty node, nothing consumed. *)
  Definition dinit (p : prog * St) : dist comp := [(([], (p.1, [])), p.2)].
End Dist.

(* ** The alternative preorder *)

Definition alt_pre `{QM : QuantumModel} (L : lifting) (p q : prog * St) : Prop :=
  ∀ (I : node → offer → Prop) (O : node → list msg) (S : node → bool),
    ext_closed S → smyth_le (SchedSts0 := dlts I O S) L (dinit p) (dinit q).

Notation "p ≼ q" := (alt_pre Stay p q) (at level 70).
Notation "p ≼ᴰ q" := (alt_pre Drop p q) (at level 70).

(* ** The alternative preorder for the almost-sure must *)

Definition alt_as `{QM : QuantumModel} (L : lifting) (p q : prog * St) : Prop :=
  ∀ (I : node → offer → Prop) (O : node → list msg) (S : node → bool),
    ext_closed S →
    pmust_as (SchedSts0 := dlts I O S) L (dinit p) → pmust_as (SchedSts0 := dlts I O S) L (dinit q).

Notation "p ≼ₐₛ q" := (alt_as Stay p q) (at level 70).
Notation "p ≼ₐₛᴰ q" := (alt_as Drop p q) (at level 70).

(* ** The uniform form: one witness of [p] for every menu under which the
    run of [q] is a run.  It is the "acceptance sets" reading of [≼]: the
    witness is chosen before the menu, so it uses only the instructions of
    the run of [q], stops only where that run stops, and its leaves refuse
    whatever the leaves of [q] at the same node refuse. *)

Definition alt_pre_unif `{QM : QuantumModel} (L : lifting) (p q : prog * St) : Prop :=
  ∀ (O : node → list msg) (S : node → bool), ext_closed S →
    ∀ (I : node → offer → Prop) r_q, is_run (SchedSts0 := dlts I O S) L (dinit q) r_q →
      ∃ r_p, run_le (SchedSts0 := dlts I O S) r_p r_q ∧
        ∀ I', is_run (SchedSts0 := dlts I' O S) L (dinit q) r_q →
              is_run (SchedSts0 := dlts I' O S) L (dinit p) r_p.

(* Along a run of 𝔻 from a non-zero memory, every component has a non-zero memory. *)
Lemma drun_nonzero `{QM : QuantumModel} L I O S (p : prog * St) r :
  p.2 ≠ szero → is_run (SchedSts0 := dlts I O S) L (dinit p) r → ∀ n x, x ∈ r n → x.2 ≠ szero.
Proof.
  intros Hp Hr. apply (@run_weights Weights_of_QuantumModel _ _ (dlts I O S) L (λ ρ, ρ ≠ szero) (cstep_nonzero I O) _ _ Hr).
  intros x Hx. apply list_elem_of_singleton in Hx. by subst x.
Qed.

Lemma alt_pre_unif_alt_pre `{QM : QuantumModel} L (p q : prog * St) : alt_pre_unif L p q → alt_pre L p q.
Proof.
  intros Hu I O S HS r_q Hr_q. destruct (Hu O S HS I r_q Hr_q) as (r_p & Hle & Hall).
  exists r_p. split; [by apply Hall|done].
Qed.
Section Follow.
  Context `{QM : QuantumModel} (I : node → offer → Prop) (O : node → list msg) (S : node → bool).

  Notation comp := (node * (prog * list msg))%type.

  Definition dstep_res (L : lifting) (𝔇 : dist comp) (it : item)
      (res : comp → St → dist comp) (𝔇' : dist comp) : Prop :=
    dmoves (SchedSts0 := dlts I O S) 𝔇 it ∧
    ∃ Δs, Forall2 (λ cρ Δ, comp_step (SchedSts0 := dlts I O S) L cρ.2 cρ.1 it Δ ∧
                     (S cρ.1.1 = false → (∃ Δ', cstep I O cρ.2 cρ.1 it Δ') → Δ = res cρ.1 cρ.2)) 𝔇 Δs
          ∧ 𝔇' = dsum Δs.

  Definition follows (L : lifting) (𝔇 : dist comp) (w : nat → item) (res : nat → comp → St → dist comp)
      (r : nat → dist comp) : Prop :=
    r 0 = 𝔇 ∧
    ∃ g : nat → nat, g 0 = 0 ∧
      ∀ n, (∃ m, g (Datatypes.S n) = g n + Datatypes.S m
                 ∧ (∀ d, d < m → ¬ dmoves (SchedSts0 := dlts I O S) (r n) (w (g n + d)))
                 ∧ dstep_res L (r n) (w (g n + m)) (res (g n + m)) (r (Datatypes.S n)))
           ∨ (dstable (SchedSts0 := dlts I O S) (r n) ∧ r (Datatypes.S n) = r n).

  Lemma follows_is_run L 𝔇 w res r : follows L 𝔇 w res r → is_run (SchedSts0 := dlts I O S) L 𝔇 r.
  Proof.
    intros (Hr0 & g & _ & Hg). split; [done|]. intros n.
    destruct (Hg n) as [(m & _ & _ & Hm & Δs & HF & ->)|Hst]; [left|by right].
    exists (w (g n + m)). split; [done|]. exists Δs. split; [|done].
    eapply Forall2_impl; [done|]. by intros ? ? [].
  Qed.
End Follow.

Definition alt_pre_det `{QM : QuantumModel} (L : lifting) (p q : prog * St) : Prop :=
  ∀ (O : node → list msg) (S : node → bool), ext_closed S →
    ∀ (I : node → offer → Prop) r_q, is_run (SchedSts0 := dlts I O S) L (dinit q) r_q →
      ∃ w res, ∀ I', is_run (SchedSts0 := dlts I' O S) L (dinit q) r_q →
        ∃ r_p, follows I' O S L (dinit p) w res r_p ∧ run_le (SchedSts0 := dlts I' O S) r_p r_q.

Lemma alt_pre_det_alt_pre `{QM : QuantumModel} L (p q : prog * St) : alt_pre_det L p q → alt_pre L p q.
Proof.
  intros Hd I O S HS r_q Hr_q. destruct (Hd O S HS I r_q Hr_q) as (w & res & Hall).
  destruct (Hall I Hr_q) as (r_p & Hr_p & Hle). exists r_p. split; [|done]. by eapply follows_is_run.
Qed.

End DistLTS.

Notation "p ≼ q" := (alt_pre Stay p q) (at level 70).
Notation "p ≼ᴰ q" := (alt_pre Drop p q) (at level 70).
Notation "p ≼ₐₛ q" := (alt_as Stay p q) (at level 70).
Notation "p ≼ₐₛᴰ q" := (alt_as Drop p q) (at level 70).

(* end hide *)
