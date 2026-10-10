(* begin hide *)
(* * Quantum states, acted upon linearly by super-operators

    Shared by the state-level results: [Harmony], [Corollaries], [Kierner]. *)
From Stdlib Require Import List.
From TestingTheory Require Import Lifted Paths.
Import ListNotations.

Class StAlg `{FinAlg} := {
  St : Type;
  szero : St;
  sadd : St -> St -> St;
  ssup : (nat -> St) -> St;
  app : T -> St -> St;
  app_one ρ : app one ρ = ρ;
  app_zero ρ : app zero ρ = szero;
  app_comp a b ρ : app (a ⋅ b) ρ = app a (app b ρ);
  app_add a b ρ : app (add a b) ρ = sadd (app a ρ) (app b ρ);
  app_szero a : app a szero = szero;
  sadd_szero : sadd szero szero = szero;
  (* Evaluation at a state commutes with suprema (pointwise limits). *)
  app_sup f g ρ : chain f -> (forall n, g n = app (f n) ρ) -> app (sup f) ρ = ssup g;
  (* A super-operator is determined by its action on states. *)
  app_ext a b : (forall ρ, app a ρ = app b ρ) -> a = b }.

Section States.
Context `{StAlg}.

Definition ssum := fold_right sadd szero.

Lemma app_ssum (l : list T) ρ : app (sum l) ρ = ssum (map (fun a => app a ρ) l).
Proof. induction l; simpl; [apply app_zero | now rewrite app_add, IHl]. Qed.

End States.
(* end hide *)
