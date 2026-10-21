(* begin hide *)
From stdpp Require Import gmap listset countable numbers.
From Stdlib Require Uint63.
From TestingTheory Require Import ActTau InputOutputActions gLts SyncActions Bisimulation
  Termination coConvergence coFiniteImage VCCS.Language.LTS VCCS.Language.gLts_Instance.
Import ListNotations.

(* Computing the waiting states of VCCS processes. *)

Section Examples.

Import Uint63.

#[local] Instance int63_eq_dec : EqDecision int := Uint63.eqs.
#[local] Instance int63_countable : Countable int := inj_countable' to_Z of_Z of_to_Z.

(* Channels are natural numbers, values are 63-bit machine integers. *)
#[local] Instance VCCS_int63 : VCCS_Parameters := {| Channel := nat; Value := int; O := 0%uint63 |}.

(* Co-convergence with the VCCS instances made explicit. *)
Definition cocnv_VCCS (p : proc) (s : list (ExtAct TypeOfActions)) : Prop :=
  @cocnv proc (ExtAct TypeOfActions) VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq)
    (ExtAct TypeOfActions) VCCS_ExtAction SyncAction_of_dual p s.

(* An internal choice between emitting on channel [0] and stopping. *)
Definition p1 : proc := g (𝛕 • g (cst 0 ! cst 0%uint63 • g 𝟘) + 𝛕 • g 𝟘).

(* An output on channel [0] in parallel with an input on channel [0] followed by an output
   on channel [1]. *)
Definition p2 : proc := g (cst 0 ! cst 0%uint63 • g 𝟘) ‖ g (cst 0 ? • g (cst 1 ! cst 0%uint63 • g 𝟘)).


(* With the empty co-trace, both branches of [p1] are stable. *)
Variable h1 : cocnv_VCCS p1 [].

Example p1_waiting : bool_decide (cowaiting_states p1 [] h1 = {[ g (cst 0 ! cst 0%uint63 • g 𝟘) ; g 𝟘 ]}) = true.
Proof. vm_compute. reflexivity. Qed.

(* After the co-trace [0?] (the observer receives on channel [0]), only the emitting branch
   could synchronise, and it ends in [𝟘]. *)
Variable h1' : cocnv_VCCS p1 [ActIn (cst 0, cst 0%uint63)].
Example p1_waiting_after_a : bool_decide (cowaiting_states p1 [ActIn (cst 0, cst 0%uint63)] h1' = {[ g 𝟘 ]}) = true.
Proof. vm_compute. reflexivity. Qed.

(* [p2] communicates internally on channel [0]: it reaches itself and the state after the
   communication, but only the latter is stable. *)
Variable h2 : cocnv_VCCS p2 [].
Example p2_reachable :
  bool_decide (coreachable_states p2 [] h2 = {[ p2 ; g 𝟘 ‖ g (cst 1 ! cst 0%uint63 • g 𝟘) ]}) = true.
Proof. vm_compute. reflexivity. Qed.

Example p2_waiting : bool_decide (cowaiting_states p2 [] h2 = {[ g 𝟘 ‖ g (cst 1 ! cst 0%uint63 • g 𝟘) ]}) = true.
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
