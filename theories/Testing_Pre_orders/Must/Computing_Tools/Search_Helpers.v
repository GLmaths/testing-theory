(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable gmap list sets.
From TestingTheory Require Import ActTau Subset_Act.
Import ListNotations.

(* Generic pieces shared by the distinguishing-test tools of the languages. *)

Section Search_Helpers.

(* Either some [S p] is included in [C], or a set [X] outside [C] meets every [S p]. *)
Definition included_or_witnesses {B : Type} `{Countable B} {Q : Type}
  (ps : list Q) (S : Q → subset_of B) (C : subset_of B) :
  (∀ p, p ∈ ps → (S p ⊆ C) + { x | x ∈ S p ∧ x ∉ C }) →
  { p | p ∈ ps ∧ S p ⊆ C }
  + { X : gset B | (∀ x, x ∈ X → x ∉ C) ∧ (∀ p, p ∈ ps → ∃ x, x ∈ X ∧ x ∈ S p) }.
Proof.
  induction ps as [| p ps IH]; intros h.
  - right. exists ∅. split.
    + intros x hx. set_solver.
    + intros p hp. by apply elem_of_nil in hp.
  - destruct (h p (list_elem_of_here p ps)) as [sub | (x & hx & hnx)].
    + left. exists p. split; [apply list_elem_of_here | exact sub].
    + destruct IH as [(p' & hp' & sub) | (X & hXC & hXS)].
      * intros p' hp'. apply h, list_elem_of_further, hp'.
      * left. exists p'. split; [apply list_elem_of_further, hp' | exact sub].
      * right. exists ({[x]} ∪ X). split.
        -- intros y [->%elem_of_singleton | hy]%elem_of_union; [exact hnx | exact (hXC y hy)].
        -- intros p0 [-> | hp0]%elem_of_cons.
           ++ exists x. split; [set_solver | exact hx].
           ++ destruct (hXS p0 hp0) as (y & hy & hyS).
              exists y. split; [set_solver | exact hyS].
Defined.

Context {A : Type}.

(* The co-traces of length [k] over [alphabet]. *)
Fixpoint traces_of_length (alphabet : list A) (k : nat) : list (trace A) :=
  match k with
  | 0 => [[]]
  | S k => flat_map (λ μ, map (cons μ) (traces_of_length alphabet k)) alphabet
  end.

(* The co-traces of length at most [n] over [alphabet], shortest first. *)
Definition traces_upto (alphabet : list A) (n : nat) : list (trace A) :=
  flat_map (traces_of_length alphabet) (seq 0 (S n)).

End Search_Helpers.

(* Either the property holds, or a distinguishing test, or a co-trace along which the
   first ([true]) or the second ([false]) process did not converge within the bound. *)
Inductive bounded_answer {A : Type} (H : Prop) (D : Type) : Type :=
| Holds : H → bounded_answer H D
| Distinguished : D → bounded_answer H D
| Timeout : trace A → bool → bounded_answer H D.

Arguments Holds {A H D}.
Arguments Distinguished {A H D}.
Arguments Timeout {A H D}.

(* The verdict without the proofs. *)
Inductive verdict {A P : Type} : Type :=
| V_holds
| V_distinguished (s : trace A) (t : P)
| V_timeout (s : trace A) (on_p : bool).

Arguments verdict : clear implicits.
(* end hide *)
