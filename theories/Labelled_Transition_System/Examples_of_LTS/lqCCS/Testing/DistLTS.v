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
    distributions of components [(n, (P, C))] weighted by a memory [ρ]:
    [n], the node, is the co-trace the component has performed with the
    observer (the co-actions, with the tag of the observer and the value or
    the outcome), and [C] the outputs the program has consumed (tag,
    channel, value), among the outputs [O n] the observer offers at that
    node.  Outputs are asynchronous: the observer does not
    see when they are consumed, so a consumption does not extend the node;
    it is a silent step of the component, [C] only prevents a second
    consumption.  The labels of [𝔻] are the choices [s] of the program (a
    silent step of every component that has it, as in [Scheduled.v], or the
    consumption of an offered output by the pair of the tags) and the
    instructions [(k, t)], "the tag [k] of the observer, answered by the tag
    [t] of the program": at every node whose menu offers an input or an
    action on the memory tagged [k], an input is served by an output of the
    program, an operation on the memory is done; the components that are not
    concerned stay.  Three parameters describe the shape of a deterministic
    observer: its menu [I n o] (the inputs and actions on the memory it
    offers at the node [n]), its outputs [O n] at the node [n], and its
    success nodes [S n], closed under extension; the successful components
    are frozen.

    The alternative preorder [≼] is the Smyth comparison of [pMust_smyth]
    in [𝔻], for every shape [(I, O, S)]: the quantification over observers
    is replaced by a quantification over shapes, and the runs of [𝔻] are
    the trees of runs of the configuration LTS following one word of choices. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Offers of the observer, co-actions, nodes, items *)

Inductive offer : Type :=
| OffOut (k : tag) (c : channel) (v : val)
| OffIn (k : tag) (c : channel)
| OffOp (k : tag) (E : sop) (qs : list qubit)
| OffMeas (k : tag) (M : meas) (qs : list qubit)
| OffInit (k : tag) (qs : list qubit).

Inductive coact : Type :=
| CoOut (k : tag) (c : channel) (v : val)
| CoIn (k : tag) (c : channel) (v : val)
| CoOp (k : tag) (E : sop) (qs : list qubit)
| CoMeas (k : tag) (M : meas) (qs : list qubit) (n : nat)
| CoInit (k : tag) (qs : list qubit).

Definition co_tag (a : coact) : tag :=
  match a with
  | CoOut k _ _ | CoIn k _ _ | CoOp k _ _ | CoMeas k _ _ _ | CoInit k _ => k
  end.

(* The action of the observer: it outputs what the program inputs. *)
Definition co_act (a : coact) : prog_action :=
  match a with
  | CoOut _ c v => PrOut c v
  | CoIn _ c v => PrIn c v
  | CoOp _ E qs => PrOp E qs
  | CoMeas _ M qs n => PrMeas M qs n
  | CoInit _ qs => PrInit qs
  end.

Definition node : Type := list coact.

Inductive item : Type :=
| ICh (s : choice)
| IOff (k : tag) (t : tag).

Definition ext_closed (S : node → bool) : Prop := ∀ n a, S n = true → S (n ++ [a]) = true.

(* A message of the observer: its tag, the channel, the value. *)
Definition msg : Type := tag * channel * val.

Definition co_of_msg (m : msg) : coact := CoOut m.1.1 m.1.2 m.2.

Section Dist.
  Context `{QM : QuantumModel}.
  Context (I : node → offer → Prop) (O : node → list msg) (S : node → bool).

  Notation comp := (node * (proc * list msg))%type.

  (* ** The step of one component *)

  Definition dual (l : Labels prog_action + mem_action) (a : prog_action) : Prop :=
    match l with
    | inl (ActExt a0) => sync_sys (inr a0) a
    | inl τ => False
    | inr b => sync_sys (inl b) a
    end.

  Definition blocking_offer (o : offer) : Prop :=
    match o with OffOut _ _ _ => False | _ => True end.

  Definition off_tag (o : offer) : tag :=
    match o with
    | OffOut k _ _ | OffIn k _ | OffOp k _ _ | OffMeas k _ _ | OffInit k _ => k
    end.

  Definition co_of (o : offer) (l : Labels prog_action + mem_action) : coact :=
    match o with
    | OffOut k c v => CoOut k c v
    | OffIn k c => CoIn k c (match l with inl (ActExt (PrOut _ v)) => v | _ => VNat 0 end)
    | OffOp k E qs => CoOp k E qs
    | OffMeas k M qs => CoMeas k M qs (match l with inr (MeMeas _ _ n) => n | _ => 0 end)
    | OffInit k qs => CoInit k qs
    end.

  Definition answers (o : offer) (l : Labels prog_action + mem_action) : Prop :=
    blocking_offer o ∧ dual l (co_act (co_of o l)).

  Definition by_tag (s : choice) (t : tag) : Prop := s = CEps ∨ s = CTag t.

  Inductive cstep (ρ : St) : comp → item → dist comp → Prop :=
  | cs_ch n P C s Δ :
      sched_step ρ P s Δ →
      cstep ρ (n, (P, C)) (ICh s) (map (λ Pρ, ((n, (Pρ.1, C)), Pρ.2)) Δ)
  | cs_recv n P C k c v t P' :
      (k, c, v) ∈ O n → k ∉ (λ m : msg, m.1.1) <$> C →
      prog_step P (CTag t) (ActExt (PrIn c v)) P' →
      cstep ρ (n, (P, C)) (ICh (cpair t k)) [((n, (P', C ++ [(k, c, v)])), ρ)]
  | cs_dual n P C o l t s Λ :
      I n o → vis_step ρ P s l Λ → by_tag s t → answers o l →
      cstep ρ (n, (P, C)) (IOff (off_tag o) t)
        (map (λ x, ((n ++ [co_of o x.1], (x.2.1, C)), x.2.2)) Λ).

  Lemma cs_in ρ n P C k c v t P' :
    I n (OffIn k c) → prog_step P (CTag t) (ActExt (PrOut c v)) P' →
    cstep ρ (n, (P, C)) (IOff k t)
      [((n ++ [CoIn k c v], (P', C)), ρ)].
  Proof.
    intros HI Hp.
    apply (cs_dual ρ n P C (OffIn k c) (inl (c ! v)) t t [(inl (c ! v), (P', ρ))] HI).
    - by apply vs_prog.
    - by right.
    - split; [done|]. apply sync_sys_chan. constructor.
  Qed.

  Lemma cs_op ρ n P C k E' qs t :
    I n (OffOp k E' qs) →
    cstep ρ (n, (P, C)) (IOff k t)
      [((n ++ [CoOp k E' qs], (P, C)), sop_apply E' qs ρ)].
  Proof.
    intros HI.
    apply (cs_dual ρ n P C (OffOp k E' qs) (inr (MeSop (sop_act E' qs))) t CEps
             [(inr (MeSop (sop_act E' qs)), (P, sop_apply E' qs ρ))] HI).
    - apply vs_sop.
    - by left.
    - split; [done|]. apply sync_sys_mem. constructor.
  Qed.

  Lemma cs_init ρ n P C k qs t :
    I n (OffInit k qs) →
    cstep ρ (n, (P, C)) (IOff k t)
      [((n ++ [CoInit k qs], (P, C)), init_apply qs ρ)].
  Proof.
    intros HI.
    apply (cs_dual ρ n P C (OffInit k qs) (inr (MeSop (init_act qs))) t CEps
             [(inr (MeSop (init_act qs)), (P, init_apply qs ρ))] HI).
    - apply vs_sop.
    - by left.
    - split; [done|]. apply sync_sys_mem. constructor.
  Qed.

  Lemma cs_meas ρ n P C k M qs t :
    I n (OffMeas k M qs) →
    cstep ρ (n, (P, C)) (IOff k t)
      (map (λ k', ((n ++ [CoMeas k M qs (code _ k')], (P, C)),
                   meas_branch M qs k' ρ))
         (outs_nz M qs ρ)).
  Proof.
    intros HI.
    pose proof (cs_dual ρ n P C (OffMeas k M qs) (inr (MeMeas M qs 0)) t CEps _ HI
                  (vs_meas ρ P M qs)) as Hd.
    rewrite map_map in Hd. apply Hd.
    - by left.
    - split; [done|]. apply sync_sys_mem. constructor.
  Qed.

  Inductive cstep_view (ρ : St) : comp → item → dist comp → Prop :=
  | cv_ch n P C s Δ :
      sched_step ρ P s Δ →
      cstep_view ρ (n, (P, C)) (ICh s) (map (λ Pρ, ((n, (Pρ.1, C)), Pρ.2)) Δ)
  | cv_recv n P C k c v t P' :
      (k, c, v) ∈ O n → k ∉ (λ m : msg, m.1.1) <$> C →
      prog_step P (CTag t) (ActExt (PrIn c v)) P' →
      cstep_view ρ (n, (P, C)) (ICh (cpair t k)) [((n, (P', C ++ [(k, c, v)])), ρ)]
  | cv_in n P C k c v t P' :
      I n (OffIn k c) → prog_step P (CTag t) (ActExt (PrOut c v)) P' →
      cstep_view ρ (n, (P, C)) (IOff k t)
        [((n ++ [CoIn k c v], (P', C)), ρ)]
  | cv_op n P C k E' qs t :
      I n (OffOp k E' qs) →
      cstep_view ρ (n, (P, C)) (IOff k t)
        [((n ++ [CoOp k E' qs], (P, C)), sop_apply E' qs ρ)]
  | cv_init n P C k qs t :
      I n (OffInit k qs) →
      cstep_view ρ (n, (P, C)) (IOff k t)
        [((n ++ [CoInit k qs], (P, C)), init_apply qs ρ)]
  | cv_meas n P C k M qs t :
      I n (OffMeas k M qs) →
      cstep_view ρ (n, (P, C)) (IOff k t)
        (map (λ k', ((n ++ [CoMeas k M qs (code _ k')], (P, C)),
                     meas_branch M qs k' ρ))
           (outs_nz M qs ρ)).

  Lemma cstep_cases ρ c it Δ : cstep ρ c it Δ → cstep_view ρ c it Δ.
  Proof.
    intros Hc. destruct Hc as [n P C s Δ Hs|n P C k c v t P' HE HC Hp|n P C o l t s Λ HI Hv Ht [Hb Hd]].
    - by apply cv_ch.
    - by apply cv_recv.
    - destruct Hv as [t0 a P' Hp|ℰ|M qs].
      + destruct Ht as [Ht|Ht]; [done|]. injection Ht as ->.
        destruct o as [k c v|k c|k E' qs|k M qs|k qs]; simpl in *; try done.
        * inversion Hd as [|? ? Hsc]; subst. destruct a; inversion Hsc; subst. by apply cv_in.
        * inversion Hd as [|? ? Hsc]; subst. inversion Hsc.
        * inversion Hd as [|? ? Hsc]; subst. inversion Hsc.
        * inversion Hd as [|? ? Hsc]; subst. inversion Hsc.
      + destruct o as [k c v|k c|k E' qs|k M qs|k qs]; simpl in *; try done.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy; subst. by apply cv_op.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy; subst. by apply cv_init.
      + destruct o as [k c v|k c|k E' qs'|k M' qs'|k qs']; simpl in *; try done.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy; subst. rewrite map_map. simpl. by apply cv_meas.
        * inversion Hd as [? ? Hsy|]; subst. inversion Hsy.
  Qed.

  #[global] Instance dlts : SchedSts comp item :=
    {| pMust_scheduled.sstep := cstep; psuccess := λ x, S x.1 = true |}.

  Lemma cstep_nonzero ρ c it Θ :
    ρ ≠ szero → cstep ρ c it Θ → ∀ x, x ∈ Θ → x.2 ≠ szero.
  Proof.
    intros Hρ Hc x Hx. apply cstep_cases in Hc. inversion Hc as [? ? ? s Δ Hs| | | | |? ? ? k M qs t HI]; subst.
    - apply list_elem_of_fmap in Hx as (Pρ & -> & HPρ). destruct Pρ as [P' ρ'].
      exact (sched_step_nonzero ρ _ _ _ Hρ Hs P' ρ' HPρ).
    - apply list_elem_of_singleton in Hx. by subst x.
    - apply list_elem_of_singleton in Hx. by subst x.
    - apply list_elem_of_singleton in Hx. subst x. by apply sop_apply_nonzero.
    - apply list_elem_of_singleton in Hx. subst x. by apply init_apply_nonzero.
    - apply list_elem_of_fmap in Hx as (k' & -> & Hk'). by apply outs_nz_spec in Hk'.
  Qed.

  (* The initial distribution: one component at the empty node, nothing consumed. *)
  Definition dinit (p : proc * St) : dist comp := [(([], (p.1, [])), p.2)].
End Dist.

(* ** The alternative preorder *)

Definition alt_pre `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ (I : node → offer → Prop) (O : node → list msg) (S : node → bool),
    ext_closed S → smyth_le (SchedSts0 := dlts I O S) L (dinit p) (dinit q).

Notation "p ≼ q" := (alt_pre Stay p q) (at level 70).
Notation "p ≼ᴰ q" := (alt_pre Drop p q) (at level 70).

(* ** The alternative preorder for the almost-sure must *)

Definition alt_as `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
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

Definition alt_pre_unif `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ (O : node → list msg) (S : node → bool), ext_closed S →
    ∀ (I : node → offer → Prop) r_q, is_run (SchedSts0 := dlts I O S) L (dinit q) r_q →
      ∃ r_p, run_le (SchedSts0 := dlts I O S) r_p r_q ∧
        ∀ I', is_run (SchedSts0 := dlts I' O S) L (dinit q) r_q →
              is_run (SchedSts0 := dlts I' O S) L (dinit p) r_p.

(* Along a run of 𝔻 from a non-zero memory, every component has a non-zero memory. *)
Lemma drun_nonzero `{QM : QuantumModel} L I O S (p : proc * St) r :
  p.2 ≠ szero → is_run (SchedSts0 := dlts I O S) L (dinit p) r → ∀ n x, x ∈ r n → x.2 ≠ szero.
Proof.
  intros Hp Hr. apply (@run_weights Weights_of_QuantumModel _ _ (dlts I O S) L (λ ρ, ρ ≠ szero) (cstep_nonzero I O) _ _ Hr).
  intros x Hx. apply list_elem_of_singleton in Hx. by subst x.
Qed.

Lemma alt_pre_unif_alt_pre `{QM : QuantumModel} L (p q : proc * St) : alt_pre_unif L p q → alt_pre L p q.
Proof.
  intros Hu I O S HS r_q Hr_q. destruct (Hu O S HS I r_q Hr_q) as (r_p & Hle & Hall).
  exists r_p. split; [by apply Hall|done].
Qed.
Section Follow.
  Context `{QM : QuantumModel} (I : node → offer → Prop) (O : node → list msg) (S : node → bool).

  Notation comp := (node * (proc * list msg))%type.

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
      ∀ n, (∃ k, g (Datatypes.S n) = g n + Datatypes.S k
                 ∧ (∀ j, j < k → ¬ dmoves (SchedSts0 := dlts I O S) (r n) (w (g n + j)))
                 ∧ dstep_res L (r n) (w (g n + k)) (res (g n + k)) (r (Datatypes.S n)))
           ∨ (dstable (SchedSts0 := dlts I O S) (r n) ∧ r (Datatypes.S n) = r n).

  Lemma follows_is_run L 𝔇 w res r : follows L 𝔇 w res r → is_run (SchedSts0 := dlts I O S) L 𝔇 r.
  Proof.
    intros (Hr0 & g & _ & Hg). split; [done|]. intros n.
    destruct (Hg n) as [(k & _ & _ & Hm & Δs & HF & ->)|Hst]; [left|by right].
    exists (w (g n + k)). split; [done|]. exists Δs. split; [|done].
    eapply Forall2_impl; [done|]. by intros ? ? [].
  Qed.
End Follow.

Definition alt_pre_det `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ (O : node → list msg) (S : node → bool), ext_closed S →
    ∀ (I : node → offer → Prop) r_q, is_run (SchedSts0 := dlts I O S) L (dinit q) r_q →
      ∃ w res, ∀ I', is_run (SchedSts0 := dlts I' O S) L (dinit q) r_q →
        ∃ r_p, follows I' O S L (dinit p) w res r_p ∧ run_le (SchedSts0 := dlts I' O S) r_p r_q.

Lemma alt_pre_det_alt_pre `{QM : QuantumModel} L (p q : proc * St) : alt_pre_det L p q → alt_pre L p q.
Proof.
  intros Hd I O S HS r_q Hr_q. destruct (Hd O S HS I r_q Hr_q) as (w & res & Hall).
  destruct (Hall I Hr_q) as (r_p & Hr_p & Hle). exists r_p. split; [|done]. by eapply follows_is_run.
Qed.
(* end hide *)
