(* begin hide *)
From TestingTheory Require Import Decision.Tools_in_construction.Tools.VCCS_Tools.
From Stdlib.Unicode Require Import Utf8.

(** Example 3: [p ⊑ₘᵤₛₜᵢ q]. *)

Definition q : proc :=
  rec 0 • g (cst 0 ? • g (cst 1 ! bvar 0 • g (cst 2 ? • g (cst 3 ! bvar 0 • g (cst 4 ? • g (cst 5 !
  bvar 0 • g (cst 6 ? • g (cst 7 ! bvar 0 • g (cst 8 ? • g (cst 9 ! bvar 0 • g (cst 10 ? • g (cst 11
  ! bvar 0 • g (cst 12 ? • g (cst 13 ! bvar 0 • g (cst 14 ? • g (cst 15 ! bvar 0 • g (cst 16 ? • g
  (cst 17 ! bvar 0 • g (cst 18 ? • g (cst 19 ! bvar 0 • g (cst 20 ? • g (cst 21 ! bvar 0 • g (cst 22
  ? • g (cst 23 ! bvar 0 • g (cst 24 ? • g (cst 25 ! bvar 0 • g (cst 26 ? • g (cst 27 ! bvar 0 • g
  (cst 28 ? • g (cst 29 ! bvar 0 • g (cst 30 ? • g (cst 31 ! bvar 0 • g (cst 32 ? • g (cst 33 ! bvar
  0 • g (cst 34 ? • g (cst 35 ! bvar 0 • g (cst 36 ? • g (cst 37 ! bvar 0 • g (cst 38 ? • g (cst 39
  ! bvar 0 • g (cst 40 ? • g (cst 41 ! bvar 0 • g (cst 42 ? • g (cst 43 ! bvar 0 • g (cst 44 ? • g
  (cst 45 ! bvar 0 • g (cst 46 ? • g (cst 47 ! bvar 0 • g (cst 48 ? • g (cst 49 ! bvar 0 • g (cst 50
  ? • g (cst 51 ! bvar 0 • g (cst 52 ? • g (cst 53 ! bvar 0 • g (cst 54 ? • g (cst 55 ! bvar 0 • g
  (cst 56 ? • g (cst 57 ! bvar 0 • g (cst 58 ? • g (cst 59 ! bvar 0 • rec 0 • g (cst 0 ? • g (cst 1
  ! bvar 0 • g (cst 2 ? • g (cst 3 ! bvar 0 • g (cst 4 ? • g (cst 5 ! bvar 0 • g (cst 6 ? • g (cst 7
  ! bvar 0 • g (cst 8 ? • g (cst 9 ! bvar 0 • g (cst 10 ? • g (cst 11 ! bvar 0 • g (cst 12 ? • g
  (cst 13 ! bvar 0 • g (cst 14 ? • g (cst 15 ! bvar 0 • g (cst 16 ? • g (cst 17 ! bvar 0 • g (cst 18
  ? • g (cst 19 ! bvar 0 • g (cst 20 ? • g (cst 21 ! bvar 0 • g (cst 22 ? • g (cst 23 ! bvar 0 • g
  (cst 24 ? • g (cst 25 ! bvar 0 • g (cst 26 ? • g (cst 27 ! bvar 0 • g (cst 28 ? • g (cst 29 ! bvar
  0 • g (cst 30 ? • g (cst 31 ! bvar 0 • g (cst 32 ? • g (cst 33 ! bvar 0 • g (cst 34 ? • g (cst 35
  ! bvar 0 • g (cst 36 ? • g (cst 37 ! bvar 0 • g (cst 38 ? • g (cst 39 ! bvar 0 • g (cst 40 ? • g
  (cst 41 ! bvar 0 • g (cst 42 ? • g (cst 43 ! bvar 0 • g (cst 44 ? • g (cst 45 ! bvar 0 • g (cst 46
  ? • g (cst 47 ! bvar 0 • g (cst 48 ? • g (cst 49 ! bvar 0 • g (cst 50 ? • g (cst 51 ! bvar 0 • g
  (cst 52 ? • g (cst 53 ! bvar 0 • g (cst 54 ? • g (cst 55 ! bvar 0 • g (cst 56 ? • g (cst 57 ! bvar
  0 • g (cst 58 ? • g (cst 59 ! bvar 0 • pr_var
  0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition p : proc :=
  ν (g (bvar 0 ! cst 7 • g 𝟘) ‖ g (bvar 0 ? • (g 𝟘 ‖ (g (𝛕 • g 𝟘) ‖ rec 0 • g (cst 0 ? • g ((𝛕 • g
  (cst 1 ! bvar 0 • g (cst 2 ? • g ((𝛕 • (If (bvar 0 == cst 7) Then g ((𝛕 • g 𝟘) + (𝛕 • g 𝟘)) Else g
  𝟘)) + (𝛕 • (g 𝟘 ‖ g (cst 3 ! bvar 0 • g (cst 4 ? • g (𝛕 • g (𝛕 • (g 𝟘 ‖ g (cst 5 ! bvar 0 • g (cst
  6 ? • g ((cst 7 ! bvar 0 • (g 𝟘 ‖ g (cst 8 ? • (g 𝟘 ‖ g (cst 9 ! bvar 0 • g (cst 10 ? • g ((𝛕 • g
  (cst 11 ! bvar 0 • (g 𝟘 ‖ g (cst 12 ? • g ((𝛕 • g (cst 13 ! bvar 0 • g (cst 14 ? • g ((𝛕 • (If
  (bvar 0 == cst 7) Then g ((𝛕 • g 𝟘) + (𝛕 • g 𝟘)) Else g 𝟘)) + (𝛕 • (g 𝟘 ‖ g (cst 15 ! bvar 0 • g
  (cst 16 ? • g (𝛕 • g (𝛕 • (g 𝟘 ‖ g (cst 17 ! bvar 0 • g (cst 18 ? • g ((cst 19 ! bvar 0 • (g 𝟘 ‖ g
  (cst 20 ? • (g 𝟘 ‖ g (cst 21 ! bvar 0 • g (cst 22 ? • g ((𝛕 • g (cst 23 ! bvar 0 • (g 𝟘 ‖ g (cst
  24 ? • g ((𝛕 • g (cst 25 ! bvar 0 • g (cst 26 ? • g ((𝛕 • (If (bvar 0 == cst 7) Then g ((𝛕 • g 𝟘)
  + (𝛕 • g 𝟘)) Else g 𝟘)) + (𝛕 • (g 𝟘 ‖ g (cst 27 ! bvar 0 • g (cst 28 ? • g (𝛕 • g (𝛕 • (g 𝟘 ‖ g
  (cst 29 ! bvar 0 • g (cst 30 ? • g ((cst 31 ! bvar 0 • (g 𝟘 ‖ g (cst 32 ? • (g 𝟘 ‖ g (cst 33 !
  bvar 0 • g (cst 34 ? • g ((𝛕 • g (cst 35 ! bvar 0 • (g 𝟘 ‖ g (cst 36 ? • g ((𝛕 • g (cst 37 ! bvar
  0 • g (cst 38 ? • g ((𝛕 • (If (bvar 0 == cst 7) Then g ((𝛕 • g 𝟘) + (𝛕 • g 𝟘)) Else g 𝟘)) + (𝛕 •
  (g 𝟘 ‖ g (cst 39 ! bvar 0 • g (cst 40 ? • g (𝛕 • g (𝛕 • (g 𝟘 ‖ g (cst 41 ! bvar 0 • g (cst 42 ? •
  g ((cst 43 ! bvar 0 • (g 𝟘 ‖ g (cst 44 ? • (g 𝟘 ‖ g (cst 45 ! bvar 0 • g (cst 46 ? • g ((𝛕 • g
  (cst 47 ! bvar 0 • (g 𝟘 ‖ g (cst 48 ? • g ((𝛕 • g (cst 49 ! bvar 0 • g (cst 50 ? • g ((𝛕 • (If
  (bvar 0 == cst 7) Then g ((𝛕 • g 𝟘) + (𝛕 • g 𝟘)) Else g 𝟘)) + (𝛕 • (g 𝟘 ‖ g (cst 51 ! bvar 0 • g
  (cst 52 ? • g (𝛕 • g (𝛕 • (g 𝟘 ‖ g (cst 53 ! bvar 0 • g (cst 54 ? • g ((cst 55 ! bvar 0 • (g 𝟘 ‖ g
  (cst 56 ? • (g 𝟘 ‖ g (cst 57 ! bvar 0 • g (cst 58 ? • g ((𝛕 • g (cst 59 ! bvar 0 • (g 𝟘 ‖ pr_var
  0))) + (𝛕 • (If (bvar 0 == cst 7) Then g 𝟘 Else g (𝛕 • g 𝟘)))))))))) + (𝛕 • ν (g (bvar 0 ! cst 0 •
  g 𝟘) ‖ g (bvar 0 ? • g 𝟘))))))))))))))))) + (𝛕 • g 𝟘)))))) + (𝛕 • (If (bvar 0 == cst 7) Then g 𝟘
  Else g (𝛕 • g 𝟘)))))))))) + (𝛕 • ν (g (bvar 0 ! cst 0 • g 𝟘) ‖ g (bvar 0 ? • g 𝟘)))))))))))))))))
  + (𝛕 • g 𝟘)))))) + (𝛕 • (If (bvar 0 == cst 7) Then g 𝟘 Else g (𝛕 • g 𝟘)))))))))) + (𝛕 • ν (g (bvar
  0 ! cst 0 • g 𝟘) ‖ g (bvar 0 ? • g 𝟘))))))))))))))))) + (𝛕 • g 𝟘)))))) + (𝛕 • (If (bvar 0 == cst
  7) Then g 𝟘 Else g (𝛕 • g 𝟘)))))))))) + (𝛕 • ν (g (bvar 0 ! cst 0 • g 𝟘) ‖ g (bvar 0 ? • g
  𝟘))))))))))))))))) + (𝛕 • g 𝟘)))))) + (𝛕 • (If (bvar 0 == cst 7) Then g 𝟘 Else g (𝛕 • g
  𝟘)))))))))) + (𝛕 • ν (g (bvar 0 ! cst 0 • g 𝟘) ‖ g (bvar 0 ? • g 𝟘))))))))))))))))) + (𝛕 • g
  𝟘))))))).

Example p_q_verdict : vccsnat_exact 400 10 1 p q = R_holds.
Proof. vm_compute. reflexivity. Qed.

Theorem p_below_q : p ⊑ₘᵤₛₜᵢ q.
Proof. exact (vccsnat_exact_holds 400 10 1 p q p_q_verdict). Qed.

(** Example 4: [p' ⋢ₘᵤₛₜᵢ q']. *)

Definition p' : proc :=
  ν (g (bvar 0 ? • (rec 0 • g (cst 0 ? • g (𝛕 • g (cst 1 ! bvar 0 • (g 𝟘 ‖ g (cst 2 ? • (g 𝟘 ‖ g (𝛕
  • g (𝛕 • g (cst 3 ! bvar 0 • g (cst 4 ? • (g 𝟘 ‖ (g 𝟘 ‖ g (cst 5 ! bvar 0 • g (𝛕 • (g 𝟘 ‖ g (cst 6
  ? • (g 𝟘 ‖ g (cst 7 ! bvar 0 • (g 𝟘 ‖ g (cst 8 ? • g (𝛕 • g (cst 9 ! bvar 0 • (g 𝟘 ‖ g (cst 10 ? •
  (g 𝟘 ‖ g (𝛕 • g (𝛕 • g (cst 11 ! bvar 0 • g (cst 12 ? • (g 𝟘 ‖ (g 𝟘 ‖ g (cst 13 ! bvar 0 • g (𝛕 •
  (g 𝟘 ‖ g (cst 14 ? • (g 𝟘 ‖ g (cst 15 ! bvar 0 • (g 𝟘 ‖ g (cst 16 ? • g (𝛕 • g (cst 17 ! bvar 0 •
  (g 𝟘 ‖ g (cst 18 ? • (g 𝟘 ‖ g (𝛕 • g (𝛕 • g (cst 19 ! bvar 0 • g (cst 20 ? • (g 𝟘 ‖ (g 𝟘 ‖ g (cst
  21 ! bvar 0 • g (𝛕 • (g 𝟘 ‖ g (cst 22 ? • (g 𝟘 ‖ g (cst 23 ! bvar 0 • (g 𝟘 ‖ g (cst 24 ? • g (𝛕 •
  g (cst 25 ! bvar 0 • (g 𝟘 ‖ g (cst 26 ? • (g 𝟘 ‖ g (𝛕 • g (𝛕 • g (cst 27 ! bvar 0 • g (cst 28 ? •
  (g 𝟘 ‖ (g 𝟘 ‖ g (cst 29 ! bvar 0 • g (𝛕 • (g 𝟘 ‖ g (cst 30 ? • (g 𝟘 ‖ g (cst 31 ! bvar 0 • (g 𝟘 ‖
  g (cst 32 ? • g (𝛕 • g (cst 33 ! bvar 0 • (g 𝟘 ‖ g (cst 34 ? • (g 𝟘 ‖ g (𝛕 • g (𝛕 • g (cst 35 !
  bvar 0 • g (cst 36 ? • (g 𝟘 ‖ (g 𝟘 ‖ g (cst 37 ! bvar 0 • g (𝛕 • (g 𝟘 ‖ g (cst 38 ? • (g 𝟘 ‖ g
  (cst 39 ! bvar 0 • (g 𝟘 ‖ g (cst 40 ? • g (𝛕 • g (cst 41 ! bvar 0 • (g 𝟘 ‖ g (cst 42 ? • (g 𝟘 ‖ g
  (𝛕 • g (𝛕 • g (cst 43 ! bvar 0 • g (cst 44 ? • (g 𝟘 ‖ (g 𝟘 ‖ g (cst 45 ! bvar 0 • g (𝛕 • (g 𝟘 ‖ g
  (cst 46 ? • (g 𝟘 ‖ g (cst 47 ! bvar 0 • (g 𝟘 ‖ g (cst 48 ? • g (𝛕 • g (cst 49 ! bvar 0 • (g 𝟘 ‖ g
  (cst 50 ? • (g 𝟘 ‖ g (𝛕 • g (𝛕 • g (cst 51 ! bvar 0 • g (cst 52 ? • (g 𝟘 ‖ (g 𝟘 ‖ g (cst 53 ! bvar
  0 • g (𝛕 • (g 𝟘 ‖ g (cst 54 ? • (g 𝟘 ‖ g (cst 55 ! bvar 0 • (g 𝟘 ‖ g (cst 56 ? • g (𝛕 • g (cst 57
  ! bvar 0 • (g 𝟘 ‖ g (cst 58 ? • (g 𝟘 ‖ g (𝛕 • g (𝛕 • g (cst 59 ! bvar 0 • pr_var
  0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ‖ g (bvar 0 ! cst 0 • g 𝟘)) ‖ g 𝟘.

Definition q' : proc :=
  g (cst 0 ? • g (cst 1 ! bvar 0 • g (cst 2 ? • g (cst 3 ! bvar 0 • g (cst 4 ? • g (cst 5 ! bvar 0 •
  g (cst 6 ? • g (cst 7 ! bvar 0 • g (cst 8 ? • g (cst 9 ! bvar 0 • g (cst 10 ? • g (cst 11 ! bvar 0
  • g (cst 12 ? • g (cst 13 ! bvar 0 • g (cst 14 ? • g (cst 15 ! bvar 0 • g (cst 16 ? • g (cst 17 !
  bvar 0 • g (cst 18 ? • g (cst 19 ! bvar 0 • g (cst 20 ? • g (cst 21 ! bvar 0 • g (cst 22 ? • g
  (cst 23 ! bvar 0 • g (cst 24 ? • g (cst 25 ! bvar 0 • g (cst 26 ? • g (cst 27 ! bvar 0 • g (cst 28
  ? • g (cst 29 ! bvar 0 • g (cst 30 ? • g (cst 31 ! bvar 0 • g (cst 32 ? • g (cst 33 ! bvar 0 • g
  (cst 34 ? • g (cst 35 ! bvar 0 • g (cst 36 ? • g (cst 37 ! bvar 0 • g (cst 38 ? • g (cst 39 ! bvar
  0 • g (cst 40 ? • g (cst 41 ! bvar 0 • g (cst 42 ? • g (cst 43 ! bvar 0 • g (cst 44 ? • g (cst 45
  ! bvar 0 • g (cst 46 ? • g (cst 47 ! bvar 0 • g (cst 48 ? • g (cst 49 ! bvar 0 • g (cst 50 ? • g
  (cst 51 ! bvar 0 • g (cst 52 ? • g (cst 53 ! bvar 0 • g (cst 54 ? • g (cst 55 ! bvar 0 • g (cst 56
  ? • g (cst 57 ! bvar 0 • g (cst 58 ? • g (cst 59 ! bvar 0 • rec 0 • g (cst 0 ? • g (cst 1 ! bvar 0
  • g (cst 2 ? • g (cst 3 ! bvar 0 • g (cst 4 ? • g (cst 5 ! bvar 0 • g (cst 6 ? • g (cst 7 ! bvar 0
  • g (cst 8 ? • g (cst 9 ! bvar 0 • g (cst 10 ? • g (cst 11 ! bvar 0 • g (cst 12 ? • (If (bvar 0 ==
  cst 7) Then g ((𝛕 • ν (g (bvar 0 ? • g 𝟘))) + (𝛕 • g (cst 13 ! bvar 0 • g (cst 14 ? • g (cst 15 !
  bvar 0 • g (cst 16 ? • g (cst 17 ! bvar 0 • g (cst 18 ? • g (cst 19 ! bvar 0 • g (cst 20 ? • g
  (cst 21 ! bvar 0 • g (cst 22 ? • g (cst 23 ! bvar 0 • g (cst 24 ? • g (cst 25 ! bvar 0 • g (cst 26
  ? • g (cst 27 ! bvar 0 • g (cst 28 ? • g (cst 29 ! bvar 0 • g (cst 30 ? • g (cst 31 ! bvar 0 • g
  (cst 32 ? • g (cst 33 ! bvar 0 • g (cst 34 ? • g (cst 35 ! bvar 0 • g (cst 36 ? • g (cst 37 ! bvar
  0 • g (cst 38 ? • g (cst 39 ! bvar 0 • g (cst 40 ? • g (cst 41 ! bvar 0 • g (cst 42 ? • g (cst 43
  ! bvar 0 • g (cst 44 ? • g (cst 45 ! bvar 0 • g (cst 46 ? • g (cst 47 ! bvar 0 • g (cst 48 ? • g
  (cst 49 ! bvar 0 • g (cst 50 ? • g (cst 51 ! bvar 0 • g (cst 52 ? • g (cst 53 ! bvar 0 • g (cst 54
  ? • g (cst 55 ! bvar 0 • g (cst 56 ? • g (cst 57 ! bvar 0 • g (cst 58 ? • g (cst 59 ! bvar 0 •
  pr_var 0))))))))))))))))))))))))))))))))))))))))))))))))) Else g (cst 13 ! bvar 0 • g (cst 14 ? •
  g (cst 15 ! bvar 0 • g (cst 16 ? • g (cst 17 ! bvar 0 • g (cst 18 ? • g (cst 19 ! bvar 0 • g (cst
  20 ? • g (cst 21 ! bvar 0 • g (cst 22 ? • g (cst 23 ! bvar 0 • g (cst 24 ? • g (cst 25 ! bvar 0 •
  g (cst 26 ? • g (cst 27 ! bvar 0 • g (cst 28 ? • g (cst 29 ! bvar 0 • g (cst 30 ? • g (cst 31 !
  bvar 0 • g (cst 32 ? • g (cst 33 ! bvar 0 • g (cst 34 ? • g (cst 35 ! bvar 0 • g (cst 36 ? • g
  (cst 37 ! bvar 0 • g (cst 38 ? • g (cst 39 ! bvar 0 • g (cst 40 ? • g (cst 41 ! bvar 0 • g (cst 42
  ? • g (cst 43 ! bvar 0 • g (cst 44 ? • g (cst 45 ! bvar 0 • g (cst 46 ? • g (cst 47 ! bvar 0 • g
  (cst 48 ? • g (cst 49 ! bvar 0 • g (cst 50 ? • g (cst 51 ! bvar 0 • g (cst 52 ? • g (cst 53 ! bvar
  0 • g (cst 54 ? • g (cst 55 ! bvar 0 • g (cst 56 ? • g (cst 57 ! bvar 0 • g (cst 58 ? • g (cst 59
  ! bvar 0 • pr_var
  0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Example p'_q'_verdict : ∃ s t, vccsnat_norm 400 10 1 p' q' = R_fails s t.
Proof. vm_compute. eexists _, _. reflexivity. Qed.

Theorem p'_not_below_q' : p' ⋢ₘᵤₛₜᵢ q'.
Proof. destruct p'_q'_verdict as (s & t & e). exact (vccsnat_norm_refutes _ _ _ _ _ s t e). Qed.

(* end hide *)
