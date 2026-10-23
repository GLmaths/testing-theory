(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act
  Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate
  coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco
  Label_Abstraction.LabelAbstraction
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses
  Computing_Tools.Search_Helpers Computing_Tools.Acceptance_Tests_Gamma Computing_Tools.Bounded_Convergence.
Import ListNotations.

(* Computing the waiting states of processes of the alternative LTS of PAL. *)

Section Examples.

#[local] Open Scope pal_scope.

Notation A := (PALA_Act nat).

(* Co-convergence with the instances made explicit. *)
Definition cocnv_PAL (p : term nat) (s : trace A) : Prop :=
  @cocnv (term nat) A (PALA_ExtAction nat) (PALA_gLts nat) A (PALA_ExtAction nat) SyncAction_of_dual p s.

(* An internal choice between emitting the tuple ⟨1⟩ and stopping. *)
Definition p1 : term nat := t_ichoice (t_out [f_actual (ve_val 1)] t_nil) t_nil.

(* After receiving a tuple, behaves as [p1]. *)
Definition q1 : term nat := t_in [f_formal 0] p1.

Variable h1 : ∀ s, cocnv_PAL p1 s.
Variable k1 : ∀ s, cocnv_PAL q1 s.

(* With the empty co-trace, both branches of the internal choice are stable. *)
Example p1_waiting :
  elements (cowaiting_states p1 [] (h1 [])) = [t_out [f_actual (ve_val 1)] t_nil; t_nil].
Proof. vm_compute. reflexivity. Qed.

(* [q1] waits for a tuple. *)
Example q1_waiting : elements (cowaiting_states q1 [] (k1 [])) = [q1].
Proof. vm_compute. reflexivity. Qed.

(* After the co-trace where the observer emits ⟨5⟩, [q1] reaches [p1] and both of its
   branches; [p1] itself is not stable (it still has to choose). *)
Example q1_reachable_after_5 :
  elements (coreachable_states q1 [AOut nat [of_val 5]] (k1 _))
  = [t_out [f_actual (ve_val 1)] t_nil; t_nil; p1].
Proof. vm_compute. reflexivity. Qed.

Example q1_waiting_after_5 :
  elements (cowaiting_states q1 [AOut nat [of_val 5]] (k1 _)) = [t_out [f_actual (ve_val 1)] t_nil; t_nil].
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
