(* begin hide *)
From Stdlib Require Import Lia.
From stdpp Require Import base countable gmap list sets numbers.
From Coinduction Require Import all.
From TestingTheory Require Import ActTau gLts SyncActions Termination Subset_Act InListPropHelper
  coWeakTransition coConvergence coFiniteImage DefinitionASrel Coin_tower_co
  Decision.Tools_in_construction.Inductive.Generic.Helpers Decision.Tools_in_construction.Inductive.Generic.Bisim
  Decision.Tools_in_construction.Inductive.Generic.Interface Decision.Tools_in_construction.Inductive.Generic.Sets Decision.Tools_in_construction.Inductive.Generic.Transport
  Decision.Tools_in_construction.Inductive.Generic.Graph Decision.Tools_in_construction.Inductive.Generic.Swaps Decision.Tools_in_construction.Inductive.Generic.Adequacy
  Decision.Tools_in_construction.Inductive.Generic.Verdict Decision.Tools_in_construction.CoInductive.Generic.Certificate Decision.Tools_in_construction.CoInductive.Generic.Antichain Decision.Tools_in_construction.CoInductive.Generic.Normalised.
Import ListNotations.

Section Auto.

Context `{TS : TraceSearchLang P A Atom PreAct T}.

(** Doubling the budgets until the procedure answers, at most [j] times. *)

Fixpoint verdict_auto (j m k n : nat) (p q : P) : result :=
  match verdict_n m k n p q with
  | R_unknown => match j with
                 | 0 => R_unknown
                 | S j => verdict_auto j (2 * m) (2 * k) n p q
                 end
  | r => r
  end.

Theorem verdict_auto_holds (j : nat) : ∀ m k n p q, verdict_auto j m k n p q = R_holds → p ≼꜀ₒ₋ₐₛ[ ts_Γ ] q.
Proof.
  induction j as [| j IH]; intros m k n p q; simpl; destruct (verdict_n m k n p q) eqn:hv; intros h; try discriminate.
  - exact (verdict_n_holds m k n p q hv).
  - exact (verdict_n_holds m k n p q hv).
  - exact (IH _ _ _ _ _ h).
Qed.

Theorem verdict_auto_fails (j : nat) : ∀ m k n p q s t, verdict_auto j m k n p q = R_fails s t → ts_must p t ∧ ¬ ts_must q t.
Proof.
  induction j as [| j IH]; intros m k n p q s t; simpl; destruct (verdict_n m k n p q) eqn:hv; intros h; try discriminate.
  - injection h as -> ->. exact (verdict_n_fails m k n p q _ _ hv).
  - injection h as -> ->. exact (verdict_n_fails m k n p q _ _ hv).
  - exact (IH _ _ _ _ _ _ _ h).
Qed.

Theorem verdict_auto_complete (j m k n : nat) (p q : P) :
  adequate m k p q = true → verdict_auto j m k n p q = R_holds ∨ ∃ s t, verdict_auto j m k n p q = R_fails s t.
Proof.
  intros ha. destruct j; simpl; destruct (verdict_n_complete m k n p q ha) as [e | (s & t & e)]; rewrite e; eauto.
Qed.

End Auto.
(* end hide *)
