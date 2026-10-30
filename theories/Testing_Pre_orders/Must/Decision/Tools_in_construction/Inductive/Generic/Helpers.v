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

End Search_Helpers.
(* end hide *)
