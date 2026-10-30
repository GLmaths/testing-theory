(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Must RelationKernel Subset_Act
  Lts_OBA Lts_FW Lts_OBA_FB LtsFW InteractionBetweenLts Testing_Predicate
  coFiniteImage coConvergence coWeakTransition DefinitionASrel CompletenessASco
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy PAL.Language.Label_Abstraction PAL_Good PAL.Testing.Must_Preorder
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses
  PAL.Characterisations.Must_Characterisation
  Decision.Computing_Tools.Bounded_Search.
Import ListNotations.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section PAL_Bounded.

Notation proc := (term nat).
Notation A := (PALA_Act nat).

Notation Γᴘᴀʟ := (λ μ : A, αᴘᴇᴠ nat (αᴛᴀᴘᴀʟ nat μ)).

#[local] Instance LtsFW_PAL : LtsFW proc A := LtsFW_of_gLtsObaFW (H0 := hyp_gLtsObaFW nat).
#[local] Instance ta_PAL : CompletenessASco.test_co_acceptance_set_spec (ta nat) Γᴘᴀʟ :=
  hyp_test_co_acceptance_set_spec nat.

#[local] Existing Instance LA_class_proj.

#[local] Instance LA_proj_PAL : LA_proj (label_ker 𝔸ᴘᴀʟ) Γᴘᴀʟ.
Proof.
  intros μ μ'. transitivity (ρ[𝔸ᴘᴀʟ] μ = ρ[𝔸ᴘᴀʟ] μ').
  - symmetry. apply ρᴘᴀʟ_eq.
  - apply (LA_proj_spec (R := label_ker 𝔸ᴘᴀʟ) (f := ρ[𝔸ᴘᴀʟ])).
Qed.

#[local] Instance LA_surj_PAL : LA_surj Γᴘᴀʟ :=
  {| LA_repr := repr_ev; LA_repr_spec := repr_ev_spec |}.

#[local] Instance Dichotomic_Γᴘᴀʟ : Dichotomic proc Γᴘᴀʟ := λ p' q' _ _, PALA_coR_dichotomy p' q'.

Definition pal_bounded_preorder (alphabet : list A) (n : nat) (p q : proc) : Prop :=
  bounded_co_preorder (gLtsP := PALA_gLts nat) Γᴘᴀʟ alphabet n p q.

Definition pal_bounded (alphabet : list A) (n k : nat) (p q : proc) :=
  bounded_verdict (gLtsP := PALA_gLts nat) (coFiniteImagegLts0 := hyp_coFiniteImage nat)
    (DΓ := Dichotomic_Γᴘᴀʟ) Γᴘᴀʟ alphabet n k p q.

Theorem pal_bounded_holds alphabet n k (p q : proc) :
  pal_bounded alphabet n k p q = B_holds → pal_bounded_preorder alphabet n p q.
Proof.
  exact (bounded_verdict_holds (gLtsP := PALA_gLts nat) (coFiniteImagegLts0 := hyp_coFiniteImage nat)
           (DΓ := Dichotomic_Γᴘᴀʟ) Γᴘᴀʟ alphabet n k p q).
Qed.

Theorem pal_bounded_test alphabet n k (p q : proc) s E :
  pal_bounded alphabet n k p q = B_distinguished s E →
  p must_pass (ta nat E s) ∧ ¬ q must_pass (ta nat E s).
Proof.
  exact (bounded_verdict_distinguishes (outcome := good_PAL nat) (gLtsEqP := PALA_gLtsEq nat)
           (coFiniteImagegLts0 := hyp_coFiniteImage nat) (gLtsEqT := PALA_gLtsEq nat)
           (gLtsOba0 := hyp_gLtsOba nat) (Testing_Predicate0 := hyp_Testing_Predicate nat)
           (Prop_of_Inter0 := hyp_Prop_of_Inter nat) (LtsFW0 := LtsFW_PAL) 𝔸ᴘᴀʟ Γᴘᴀʟ
           (LA_proj0 := LA_proj_PAL) (LA_surj0 := LA_surj_PAL) (DΓ := Dichotomic_Γᴘᴀʟ)
           (ta := ta nat) (ta_spec := ta_PAL) alphabet n k p q s E).
Qed.

Corollary pal_bounded_refutes alphabet n k (p q : proc) s E :
  pal_bounded alphabet n k p q = B_distinguished s E → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  intros e hpre. destruct (pal_bounded_test alphabet n k p q s E e) as [hp hq].
  exact (hq (hpre _ hp)).
Qed.

Definition pal_holds_b (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  match pal_bounded alphabet n k p q with B_holds => true | _ => false end.

Theorem pal_holds_b_spec alphabet n k (p q : proc) :
  pal_holds_b alphabet n k p q = true → pal_bounded_preorder alphabet n p q.
Proof.
  unfold pal_holds_b. destruct (pal_bounded alphabet n k p q) eqn:e; try discriminate.
  intros _. exact (pal_bounded_holds alphabet n k p q e).
Qed.

Definition pal_refuted_b (alphabet : list A) (n k : nat) (p q : proc) : bool :=
  match pal_bounded alphabet n k p q with B_distinguished _ _ => true | _ => false end.

Corollary pal_refuted_b_spec alphabet n k (p q : proc) :
  pal_refuted_b alphabet n k p q = true → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof.
  unfold pal_refuted_b. destruct (pal_bounded alphabet n k p q) as [| s E |] eqn:e; try discriminate.
  intros _. exact (pal_bounded_refutes alphabet n k p q s E e).
Qed.

Corollary pal_bounded_of_must alphabet n (p q : proc) :
  p ᴘᴀʟ⊑ₘᵤₛₜᵢ q → pal_bounded_preorder alphabet n p q.
Proof.
  intros h%PAL_Alt_equivalence.
  exact (bounded_of_co_preorder (gLtsEqP := PALA_gLtsEq nat) (gLtsEqT := PALA_gLtsEq nat) 𝔸ᴘᴀʟ Γᴘᴀʟ
           (LA_proj0 := LA_proj_PAL) alphabet n p q h).
Qed.

Definition pal_test_of_not_bounded (alphabet : list A) (n k : nat) (p q : proc) (hn : ¬ pal_bounded_preorder alphabet n p q) :=
  bounded_test_of_not (outcome := good_PAL nat) (gLtsEqP := PALA_gLtsEq nat)
    (coFiniteImagegLts0 := hyp_coFiniteImage nat) (gLtsEqT := PALA_gLtsEq nat)
    (gLtsOba0 := hyp_gLtsOba nat) (Testing_Predicate0 := hyp_Testing_Predicate nat)
    (Prop_of_Inter0 := hyp_Prop_of_Inter nat) (LtsFW0 := LtsFW_PAL) 𝔸ᴘᴀʟ Γᴘᴀʟ
    (LA_proj0 := LA_proj_PAL) (LA_surj0 := LA_surj_PAL) (DΓ := Dichotomic_Γᴘᴀʟ)
    (ta := ta nat) (ta_spec := ta_PAL) alphabet n k p q hn.

End PAL_Bounded.

Section PAL_Bounded_nat.

Fixpoint arities (E : term nat) : list nat :=
  match E with
  | t_nil | t_undef | t_pvar _ | t_success => []
  | t_out t E | t_in t E | t_read t E => length t :: arities E
  | t_rec _ E => arities E
  | t_eval E1 E2 | t_if _ E1 E2 | t_ichoice E1 E2 | t_echoice E1 E2
  | t_par E1 E2 | t_lmerge E1 E2 | t_cmerge E1 E2 => arities E1 ++ arities E2
  end.

Fixpoint words {X : Type} (fs : list X) (a : nat) : list (list X) :=
  match a with
  | 0 => [[]]
  | S a => flat_map (λ f, map (cons f) (words fs a)) fs
  end.

Definition pal_alphabet (b : nat) (q : term nat) : list (PALA_Act nat) :=
  let vs := seq 0 (2 ^ b) in
  let ofs := @of_star nat :: map (@of_val nat) vs in
  let lfs := @lf_star nat :: map (@lf_val nat) vs ++ map (@lf_formal nat) vs in
  flat_map (λ a, map (@AOut nat) (words ofs a) ++ map (@AIn nat) (words lfs a)) (remove_dups (arities q)).

Definition pal_bounded_preorder_nat (b n : nat) (p q : term nat) : Prop :=
  pal_bounded_preorder (pal_alphabet b q) n p q.

Definition pal_bounded_nat (b n k : nat) (p q : term nat) :=
  pal_bounded (pal_alphabet b q) n k p q.

Definition pal_holds_nat (b n k : nat) (p q : term nat) : bool :=
  pal_holds_b (pal_alphabet b q) n k p q.

Theorem pal_holds_nat_spec b n k (p q : term nat) :
  pal_holds_nat b n k p q = true → pal_bounded_preorder_nat b n p q.
Proof. exact (pal_holds_b_spec (pal_alphabet b q) n k p q). Qed.

Definition pal_refuted_nat (b n k : nat) (p q : term nat) : bool :=
  pal_refuted_b (pal_alphabet b q) n k p q.

Theorem pal_refuted_nat_spec b n k (p q : term nat) :
  pal_refuted_nat b n k p q = true → ¬ p ᴘᴀʟ⊑ₘᵤₛₜᵢ q.
Proof. exact (pal_refuted_b_spec (pal_alphabet b q) n k p q). Qed.

Theorem pal_bounded_nat_test b n k (p q : term nat) s E :
  pal_bounded_nat b n k p q = B_distinguished s E →
  p must_pass (ta nat E s) ∧ ¬ q must_pass (ta nat E s).
Proof. exact (pal_bounded_test (pal_alphabet b q) n k p q s E). Qed.

Corollary pal_bounded_nat_of_must b n (p q : term nat) :
  p ᴘᴀʟ⊑ₘᵤₛₜᵢ q → pal_bounded_preorder_nat b n p q.
Proof. exact (pal_bounded_of_must (pal_alphabet b q) n p q). Qed.

Definition pal_test_of_not_bounded_nat (b n k : nat) (p q : term nat) (hn : ¬ pal_bounded_preorder_nat b n p q) :=
  pal_test_of_not_bounded (pal_alphabet b q) n k p q hn.

End PAL_Bounded_nat.

Section Examples.

#[local] Open Scope pal_scope.

Definition p1 : term nat := t_out [f_actual (ve_val 1)] t_nil.
Definition q1 : term nat := t_ichoice p1 t_nil.
Definition ω : term nat := t_undef.

Example p1_q1_verdict :
  match pal_bounded_nat 1 2 5 p1 q1 with B_distinguished s E => Some (s, length (elements E)) | _ => None end
  = Some ([], 1).
Proof. vm_compute. reflexivity. Qed.

Theorem p1_not_below_q1 : ¬ p1 ᴘᴀʟ⊑ₘᵤₛₜᵢ q1.
Proof. apply (pal_refuted_nat_spec 1 2 5). vm_compute. reflexivity. Qed.

Lemma q1_below_p1_bounded : pal_bounded_preorder_nat 1 2 q1 p1.
Proof. apply (pal_holds_nat_spec 1 2 5). vm_compute. reflexivity. Qed.

Example ω_timeout :
  match pal_bounded_nat 1 2 5 ω p1 with B_timeout s b => Some (s, b) | _ => None end = Some ([], true).
Proof. vm_compute. reflexivity. Qed.

End Examples.
(* end hide *)
