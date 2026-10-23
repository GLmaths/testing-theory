(* begin hide *)
From stdpp Require Import gmap gmultiset countable numbers.
From Stdlib Require Uint63.
From TestingTheory Require Import ActTau InputOutputActions gLts SyncActions Bisimulation
  Termination coConvergence coFiniteImage InteractionBetweenLts MultisetLTSConstruction
  ForwarderConstruction VACCS.Language.LTS VACCS.Language.gLts_Instance.
Import ListNotations.

(* Computing the waiting states of VACCS processes. *)

Section Examples.

Import Uint63.

#[local] Instance int63_eq_dec : EqDecision int := Uint63.eqs.
#[local] Instance int63_countable : Countable int := inj_countable' to_Z of_Z of_to_Z.

(* Channels are natural numbers, values are 63-bit machine integers. *)
#[local] Instance VACCS_int63 : VACCS_Parameters := {| Channel := nat; Value := int; O := 0%uint63 |}.

#[local] Instance SyncAction_VACCS : SyncAction (ExtAct TypeOfActions) (ExtAct TypeOfActions) :=
  SyncAction_of_dual.

Notation A := (ExtAct TypeOfActions).
Notation FW := (proc * MO A)%type.

(* The waiting states with the mailboxes as lists, to display them. *)
Definition show (X : gset FW) : list (proc * list A) := map (λ x, (x.1, elements x.2)) (elements X).

(* An internal choice between emitting on channel [0] and stopping. *)
Definition p1 : proc := g ((𝛕 • (cst 0 ! cst 0%uint63 • 𝟘)) + (𝛕 • g 𝟘)).

(* After receiving on [2], emits on [0]. *)
Definition p2 : proc := g (cst 2 ? • (cst 0 ! cst 0%uint63 • 𝟘)).

Variable h1 : ∀ s : trace A, (p1 ▷ ∅ : FW) ⇓ᶜᵒ s.
Variable h2 : ∀ s : trace A, (p2 ▷ ∅ : FW) ⇓ᶜᵒ s.

(* With the empty co-trace, both branches of [p1] are stable, with an empty mailbox. *)
Example p1_waiting :
  show (cowaiting_states (p1 ▷ ∅ : FW) [] (h1 [])) = [(cst 0 ! cst 0%uint63 • 𝟘, []); (g 𝟘, [])].
Proof. vm_compute. reflexivity. Qed.

(* [p2] waits for a message on [2]. *)
Example p2_waiting :
  show (cowaiting_states (p2 ▷ ∅ : FW) [] (h2 [])) = [(g (cst 2 ? • (cst 0 ! cst 0%uint63 • 𝟘)), [])].
Proof. vm_compute. reflexivity. Qed.

(* After the co-trace [2!0] (the observer sends [0] on channel [2]), the message goes into
   the mailbox, then [p2] consumes it: the state with the message pending is reachable
   but not stable. *)
Example p2_reachable_after_2 :
  show (coreachable_states (p2 ▷ ∅ : FW) [ActOut (cst 2, cst 0%uint63)] (h2 _))
  = [(cst 0 ! cst 0%uint63 • 𝟘, []);
     (g (cst 2 ? • (cst 0 ! cst 0%uint63 • 𝟘)), [ActOut (cst 2, cst 0%uint63)])].
Proof. vm_compute. reflexivity. Qed.

Example p2_waiting_after_2 :
  show (cowaiting_states (p2 ▷ ∅ : FW) [ActOut (cst 2, cst 0%uint63)] (h2 _))
  = [(cst 0 ! cst 0%uint63 • 𝟘, [])].
Proof. vm_compute. reflexivity. Qed.

(* A message on channel [5] is accepted by the forwarder but never consumed by [p2]: it
   stays in the mailbox of the waiting state. *)
Example p2_waiting_after_5 :
  show (cowaiting_states (p2 ▷ ∅ : FW) [ActOut (cst 5, cst 0%uint63)] (h2 _))
  = [(g (cst 2 ? • (cst 0 ! cst 0%uint63 • 𝟘)), [ActOut (cst 5, cst 0%uint63)])].
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
