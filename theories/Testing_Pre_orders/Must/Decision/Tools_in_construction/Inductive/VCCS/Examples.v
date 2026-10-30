(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import sets gmap gmultiset countable numbers list.
From TestingTheory Require Import VCCS.Testing.ta_tc_gen DefinitionAS Equivalence Must
  ParallelLTSConstruction InteractionBetweenLts Bisimulation
  ActTau InputOutputActions Convergence Termination InListPropHelper
  gLts Lts_OBA FiniteImageLTS Testing_Predicate Completeness Lts_FW Lts_OBA_FB MultisetLTSConstruction
  SetLTSConstruction ForwarderConstruction.
From TestingTheory Require Import coFiniteImage coConvergence coWeakTransition DefinitionASrel
  CompletenessASco EquivalenceASco TestSpecBridge SyncActions
  VCCS.Language.LTS VCCS.Language.gLts_Instance VCCS.Language.Label_Abstraction
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Subset_Act
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Acceptance_Tests_Gamma
  Decision.Tools_in_construction.Inductive.VCCS.Tests VCCS.Helper.Value_Swap VCCS.Characterisations.Must_Characterisation
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.Inductive.VCCS.Instance.
Import ListNotations.

#[local] Instance VCCS_nat : VCCS_Parameters := {| Channel := nat; Value := nat; O := 0 |}.

Section Examples.

Definition p1 : proc := g (cst 0 ! cst 0 • g 𝟘).
Definition q1 : proc := g ((𝛕 • g (cst 0 ! cst 0 • g 𝟘)) + (𝛕 • g 𝟘)).

Example p1_q1_verdict : vccs_verdict (VP := VCCS_nat) 20 5 2 p1 q1 = R_fails (A := ExtAct (@TypeOfActions VCCS_nat)) (T := @proc VCCS_nat) [] (g ((cst 0 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Lemma p1_not_below_q1 : p1 ⋢ₘᵤₛₜᵢ q1.
Proof. exact (vccs_verdict_refutes _ _ _ _ _ _ _ p1_q1_verdict). Qed.

Lemma q1_below_p1 : q1 ⊑ₘᵤₛₜᵢ p1.
Proof. apply (vccs_verdict_holds 20 5 2). vm_compute. reflexivity. Qed.

Definition ω : proc := rec 0 • (pr_var 0).
Definition ω_tau : proc := rec 0 • g (𝛕 • pr_var 0).
Definition ω_par : proc := rec 0 • (pr_var 0 ‖ g (cst 0 ! cst 0 • g 𝟘)).

Lemma ω_below_p1 : ω ⊑ₘᵤₛₜᵢ p1.
Proof. apply (vccs_verdict_holds 20 5 2). vm_compute. reflexivity. Qed.

Example p1_ω_verdict : vccs_verdict (VP := VCCS_nat) 20 5 2 p1 ω = R_fails (A := ExtAct (@TypeOfActions VCCS_nat)) (T := @proc VCCS_nat) [] (gen_conv []).
Proof. vm_compute. reflexivity. Qed.

Lemma p1_not_below_ω : p1 ⋢ₘᵤₛₜᵢ ω.
Proof. exact (vccs_verdict_refutes _ _ _ _ _ _ _ p1_ω_verdict). Qed.

Lemma p1_not_below_ω_tau : p1 ⋢ₘᵤₛₜᵢ ω_tau.
Proof. apply (vccs_verdict_refutes (VP := VCCS_nat) 20 5 2 _ _ [] (gen_conv [])). vm_compute. reflexivity. Qed.

Lemma p1_not_below_ω_par : p1 ⋢ₘᵤₛₜᵢ ω_par.
Proof. apply (vccs_verdict_refutes (VP := VCCS_nat) 20 5 2 _ _ [] (gen_conv [])). vm_compute. reflexivity. Qed.

Definition p2 : proc := g ((cst 0 ! cst 0 • g 𝟘) + (cst 1 ! cst 0 • g 𝟘)).
Definition q2 : proc := g (cst 0 ! cst 0 • g 𝟘).

Example p2_q2_verdict : vccs_verdict (VP := VCCS_nat) 20 5 2 p2 q2 = R_fails (A := ExtAct (@TypeOfActions VCCS_nat)) (T := @proc VCCS_nat) [] (g ((cst 1 ? • g ①) + 𝟘)).
Proof. vm_compute. reflexivity. Qed.

Definition p3 : proc := g (cst 2 ? • g (cst 0 ! cst 0 • g 𝟘)).
Definition q3 : proc := g (cst 2 ? • g ((𝛕 • g (cst 0 ! cst 0 • g 𝟘)) + (𝛕 • g 𝟘))).

Example p3_q3_verdict : ∃ s t, vccs_verdict (VP := VCCS_nat) 20 5 2 p3 q3 = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Lemma q3_below_p3 : q3 ⊑ₘᵤₛₜᵢ p3.
Proof. apply (vccs_verdict_holds 20 5 2). vm_compute. reflexivity. Qed.

Definition loop0 : proc := rec 0 • g (cst 0 ! cst 0 • pr_var 0).

Lemma loop0_refl : loop0 ⊑ₘᵤₛₜᵢ loop0.
Proof. apply (vccs_verdict_holds 20 5 2). vm_compute. reflexivity. Qed.

Definition ext_loop : proc :=
  rec 0 • g ((cst 0 ! cst 0 • pr_var 0) + (cst 1 ! cst 0 • pr_var 0)).
Definition int_loop : proc :=
  rec 0 • g ((𝛕 • g (cst 0 ! cst 0 • pr_var 0)) + (𝛕 • g (cst 1 ! cst 0 • pr_var 0))).

Lemma int_below_ext : int_loop ⊑ₘᵤₛₜᵢ ext_loop.
Proof. apply (vccs_verdict_holds 20 5 2). vm_compute. reflexivity. Qed.

Example ext_int_verdict : ∃ s t, vccs_verdict (VP := VCCS_nat) 20 5 2 ext_loop int_loop = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Example p3_q3_graph_test :
  vccs_verdict (VP := VCCS_nat) 20 5 0 p3 q3
  = R_fails (A := ExtAct (@TypeOfActions VCCS_nat)) (T := @proc VCCS_nat) [ActOut (cst 2, cst 0)]
      (g ((cst 2 ! cst 0 • g ((cst 0 ? • g ①) + 𝟘)) + (𝛕 • g ①))).
Proof. vm_compute. reflexivity. Qed.

Lemma p3_not_below_q3' : p3 ⋢ₘᵤₛₜᵢ q3.
Proof. exact (vccs_verdict_refutes _ _ _ _ _ _ _ p3_q3_graph_test). Qed.

Definition garbage : proc := rec 0 • g (cst 1 ! cst 0 • (g 𝟘 ‖ pr_var 0)).

Lemma garbage_refl : garbage ⊑ₘᵤₛₜᵢ garbage.
Proof. apply (vccs_verdict_holds 20 5 0). vm_compute. reflexivity. Qed.

End Examples.

Section Examples_Values.

Definition echo : proc := rec 0 • g (cst 0 ? • g (cst 1 ! bvar 0 • pr_var 0)).
Definition echo5 : proc := rec 0 • g (cst 0 ? • g (cst 1 ! cst 5 • pr_var 0)).
Definition filter5 : proc := g (cst 0 ? • (If (bvar 0 == cst 5) Then g (cst 1 ! cst 0 • g 𝟘) Else g 𝟘)).
Definition filter5i : proc :=
  g (cst 0 ? • (If (bvar 0 == cst 5) Then g ((𝛕 • g (cst 1 ! cst 0 • g 𝟘)) + (𝛕 • g 𝟘)) Else g 𝟘)).
Definition sink : proc := g (cst 0 ? • g 𝟘).

Lemma echo_refl : echo ⊑ₘᵤₛₜᵢ echo.
Proof. apply (vccs_verdict_holds 50 5 2). vm_compute. reflexivity. Qed.

Example echo_echo5_verdict : ∃ s t, vccs_verdict (VP := VCCS_nat) 50 5 2 echo echo5 = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Definition echo2 : proc := echo ‖ echo.

Lemma echo2_refl : echo2 ⊑ₘᵤₛₜᵢ echo2.
Proof. apply (vccs_verdict_holds 50 5 2). vm_compute. reflexivity. Qed.

Lemma filter5i_below_filter5 : filter5i ⊑ₘᵤₛₜᵢ filter5.
Proof. apply (vccs_verdict_holds 50 5 2). vm_compute. reflexivity. Qed.

Example filter5_sink_verdict : ∃ s t, vccs_verdict (VP := VCCS_nat) 50 5 2 filter5 sink = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

End Examples_Values.
(* end hide *)
