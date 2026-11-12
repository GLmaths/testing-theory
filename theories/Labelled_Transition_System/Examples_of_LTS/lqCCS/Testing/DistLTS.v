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
    distributions of components [(n, (P, C, E))] weighted by a memory [ρ]:
    [n], the node, is the co-trace the component has performed with the
    observer (the co-actions, with the tag of the observer and the value or
    the outcome), [E] the outputs the observer offers at that node, recorded
    when the node is reached, and [C] the outputs the program has consumed
    (tag, channel, value).  Outputs are asynchronous: the observer does not
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
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled.

#[local] Open Scope lqccs_scope.

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

  Notation comp := (node * (proc * list msg * list msg))%type.

  (* ** The step of one component *)

  Inductive cstep (ρ : St) : comp → item → dist comp → Prop :=
  | cs_ch n P C E s Δ :
      sched_step ρ P s Δ →
      cstep ρ (n, (P, C, E)) (ICh s) (map (λ Pρ, ((n, (Pρ.1, C, E)), Pρ.2)) Δ)
  | cs_recv n P C E k c v t P' :
      (k, c, v) ∈ E → k ∉ (λ m : msg, m.1.1) <$> C →
      prog_step P (CTag t) (ActExt (PrIn c v)) P' →
      cstep ρ (n, (P, C, E)) (ICh (cpair t k)) [((n, (P', C ++ [(k, c, v)], E)), ρ)]
  | cs_in n P C E k c v t P' :
      I n (OffIn k c) → prog_step P (CTag t) (ActExt (PrOut c v)) P' →
      cstep ρ (n, (P, C, E)) (IOff k t)
        [((n ++ [CoIn k c v], (P', C, O (n ++ [CoIn k c v]))), ρ)]
  | cs_op n P C E k E' qs t :
      I n (OffOp k E' qs) →
      cstep ρ (n, (P, C, E)) (IOff k t)
        [((n ++ [CoOp k E' qs], (P, C, O (n ++ [CoOp k E' qs]))), sop_apply E' qs ρ)]
  | cs_init n P C E k qs t :
      I n (OffInit k qs) →
      cstep ρ (n, (P, C, E)) (IOff k t)
        [((n ++ [CoInit k qs], (P, C, O (n ++ [CoInit k qs]))), init_apply qs ρ)]
  | cs_meas n P C E k M qs t :
      I n (OffMeas k M qs) →
      cstep ρ (n, (P, C, E)) (IOff k t)
        (map (λ k', ((n ++ [CoMeas k M qs (code _ k')], (P, C, O (n ++ [CoMeas k M qs (code _ k')]))),
                     meas_branch M qs k' ρ))
           (outs_nz M qs ρ)).

  #[global] Instance dlts : SchedSts comp item :=
    {| pMust_scheduled.sstep := cstep; psuccess := λ x, S x.1 = true |}.

  Lemma cstep_nonzero ρ c it Θ :
    ρ ≠ szero → cstep ρ c it Θ → ∀ x, x ∈ Θ → x.2 ≠ szero.
  Proof.
    intros Hρ Hc x Hx. inversion Hc as [? ? ? ? s Δ Hs| | | | |? ? ? ? k M qs t HI]; subst.
    - apply list_elem_of_fmap in Hx as (Pρ & -> & HPρ). destruct Pρ as [P' ρ'].
      exact (sched_step_nonzero ρ _ _ _ Hρ Hs P' ρ' HPρ).
    - apply list_elem_of_singleton in Hx. by subst x.
    - apply list_elem_of_singleton in Hx. by subst x.
    - apply list_elem_of_singleton in Hx. subst x. by apply sop_apply_nonzero.
    - apply list_elem_of_singleton in Hx. subst x. by apply init_apply_nonzero.
    - apply list_elem_of_fmap in Hx as (k' & -> & Hk'). by apply outs_nz_spec in Hk'.
  Qed.

  (* The initial distribution: one component at the empty node, nothing consumed. *)
  Definition dinit (p : proc * St) : dist comp := [(([], (p.1, [], O [])), p.2)].
End Dist.

(* ** The alternative preorder *)

Definition alt_pre `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ (I : node → offer → Prop) (O : node → list msg) (S : node → bool),
    ext_closed S → smyth_le (SchedSts0 := dlts I O S) L (dinit O p) (dinit O q).

Notation "p ≼ q" := (alt_pre Stay p q) (at level 70).
Notation "p ≼ᴰ q" := (alt_pre Drop p q) (at level 70).

(* ** The alternative preorder for the almost-sure must *)

Definition alt_as `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ (I : node → offer → Prop) (O : node → list msg) (S : node → bool),
    ext_closed S →
    pmust_as (SchedSts0 := dlts I O S) L (dinit O p) → pmust_as (SchedSts0 := dlts I O S) L (dinit O q).

Notation "p ≼ₐₛ q" := (alt_as Stay p q) (at level 70).
Notation "p ≼ₐₛᴰ q" := (alt_as Drop p q) (at level 70).

(* ** The uniform form: one witness of [p] for every menu under which the
    run of [q] is a run.  It is the "acceptance sets" reading of [≼]: the
    witness is chosen before the menu, so it uses only the instructions of
    the run of [q], stops only where that run stops, and its leaves refuse
    whatever the leaves of [q] at the same node refuse. *)

Definition alt_pre_unif `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ (O : node → list msg) (S : node → bool), ext_closed S →
    ∀ (I : node → offer → Prop) r_q, is_run (SchedSts0 := dlts I O S) L (dinit O q) r_q →
      ∃ r_p, run_le (SchedSts0 := dlts I O S) r_p r_q ∧
        ∀ I', is_run (SchedSts0 := dlts I' O S) L (dinit O q) r_q →
              is_run (SchedSts0 := dlts I' O S) L (dinit O p) r_p.

(* Along a run of 𝔻 from a non-zero memory, every component has a non-zero memory. *)
Lemma drun_nonzero `{QM : QuantumModel} L I O S (p : proc * St) r :
  p.2 ≠ szero → is_run (SchedSts0 := dlts I O S) L (dinit O p) r → ∀ n x, x ∈ r n → x.2 ≠ szero.
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

  Notation comp := (node * (proc * list msg * list msg))%type.

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
    ∀ (I : node → offer → Prop) r_q, is_run (SchedSts0 := dlts I O S) L (dinit O q) r_q →
      ∃ w res, ∀ I', is_run (SchedSts0 := dlts I' O S) L (dinit O q) r_q →
        ∃ r_p, follows I' O S L (dinit O p) w res r_p ∧ run_le (SchedSts0 := dlts I' O S) r_p r_q.

Lemma alt_pre_det_alt_pre `{QM : QuantumModel} L (p q : proc * St) : alt_pre_det L p q → alt_pre L p q.
Proof.
  intros Hd I O S HS r_q Hr_q. destruct (Hd O S HS I r_q Hr_q) as (w & res & Hall).
  destruct (Hall I Hr_q) as (r_p & Hr_p & Hle). exists r_p. split; [|done]. by eapply follows_is_run.
Qed.
(* end hide *)
