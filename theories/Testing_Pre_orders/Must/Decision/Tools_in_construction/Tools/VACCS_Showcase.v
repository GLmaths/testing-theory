(* begin hide *)
From TestingTheory Require Import Decision.Tools_in_construction.Tools.VACCS_Tools.
From Stdlib.Unicode Require Import Utf8.

Definition unreliableW : proc :=
  pr_rec 0 (𝛕 • (cst 0 ! cst 0 • 𝟘)
            + (cst 1 ? • (𝛕 • ((cst 2 ! cst 0 • 𝟘) ‖ pr_var 0)
                             + 𝛕 • (cst 3 ! cst 0 • 𝟘)))).

Definition reliableW : proc :=
  pr_rec 0 (𝛕 • (cst 0 ! cst 0 • 𝟘)
            + (cst 1 ? • ((cst 2 ! cst 0 • 𝟘) ‖ pr_var 0))).

Example reliable_unreliable_verdict : ∃ s t, vaccsnat_exact 0 10 2 reliableW unreliableW = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Theorem reliable_not_below_unreliable : reliableW ⋢ₘᵤₛₜᵢ unreliableW.
Proof. destruct reliable_unreliable_verdict as (s & t & e). exact (vaccsnat_exact_refutes _ _ _ _ _ s t e). Qed.

(* end hide *)
