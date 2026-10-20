(* begin hide *)
Require Import core unscoped.
Require Import Setoid Morphisms Relation_Definitions.
From stdpp Require base countable.

Class Pi_Values := {
  Value : Type;
  Value_eq_dec :: stdpp.base.EqDecision Value;
  Value_countable :: stdpp.countable.Countable Value;
}.
(* Parameter Channel : Type. *)
(* end hide *)
