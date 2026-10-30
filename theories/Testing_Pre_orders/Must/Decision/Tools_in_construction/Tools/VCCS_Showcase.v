(* begin hide *)
From TestingTheory Require Import Decision.Tools_in_construction.Tools.VCCS_Tools.
From Stdlib.Unicode Require Import Utf8.

Definition z7 : nat := 7.

(** Example 1: [p ⊑ₘᵤₛₜᵢ q]. *)

Definition q : proc :=
  rec 0 • g (cst 0 ? • g (cst 1 ! bvar 0 • pr_var 0)).

Definition p : proc :=
  ν (g (bvar 0 ! cst z7 • g 𝟘) ‖ g (bvar 0 ? •
  (g 𝟘 ‖ (g (𝛕 • g 𝟘) ‖
    rec 0 • g (cst 0 ? •
      (If (bvar 0 == cst z7)
       Then g ((𝛕 • g (cst 1 ! bvar 0 • pr_var 0)) + (𝛕 • ν (g (bvar 0 ! cst 0 • g 𝟘) ‖ g (bvar 0 ? • g 𝟘))))
       Else g (𝛕 • g (cst 1 ! bvar 0 •
                       g (cst 0 ? • (g 𝟘 ‖ g (𝛕 • g (cst 1 ! bvar 0 • pr_var 0)))))))))))).

Example p_q_verdict : vccsnat_norm 50 10 1 p q = R_holds.
Proof. vm_compute. reflexivity. Qed.

Theorem p_below_q : p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccsnat_norm_holds 50 10 1 p q p_q_verdict). Qed.

(** Example 2: [p' ⋢ₘᵤₛₜᵢ q']. *)

Definition p' : proc :=
  rec 0 • g (cst 0 ? • g (cst 1 ! bvar 0 • pr_var 0)) ‖
  rec 0 • g (cst 2 ? • g (cst 3 ! bvar 0 • pr_var 0)).

Definition q' : proc :=
  rec 0 • g ((cst 0 ? • g (cst 1 ! bvar 0 • pr_var 0)) +
             (cst 2 ? • (If (bvar 0 == cst z7)
                         Then g ((𝛕 • ν (g (bvar 0 ? • g 𝟘))) + (𝛕 • g (cst 3 ! bvar 0 • pr_var 0)))
                         Else g (cst 3 ! bvar 0 • pr_var 0)))).

Example p'_q'_verdict : ∃ s t, vccsnat_exact 50 10 1 p' q' = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Theorem p'_not_below_q' : p' ⋢ₘᵤₛₜᵢ q'.
Proof. destruct p'_q'_verdict as (s & t & e). exact (vccsnat_exact_refutes _ _ _ _ _ s t e). Qed.

(* end hide *)
