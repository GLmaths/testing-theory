From Must.pi Require Import Renamings.

Parameter Eval_Eq : Equation -> (option bool).
Parameter Eq_Subst_Spec : (nat -> nat) -> Prop.
Parameter Eq_Subst_Spec_inj : forall σ, injective σ -> Eq_Subst_Spec σ.
Parameter Eq_Subst_Spec_lift : forall σ, Eq_Subst_Spec σ -> Eq_Subst_Spec (up_ren σ).
Parameter Eval_Eq_Spec : forall E σ, Eq_Subst_Spec σ -> Eval_Eq (ren1 σ E) = Eval_Eq E.

(* Definition of the LTS *)
Definition is_bound_out (a:Act) : bool :=
  match a with
  | BoundOut _ => true
  | _ => false
  end.

Notation "a '⇑?' p" := (if is_bound_out a then ⇑ p else p) (at level 20).
Notation "a '?↔' p" := (if is_bound_out a then p ⟨swap⟩ else p) (at level 20).

Lemma Shift_Through_Questions : forall a (p:proc),
  ⇑ (a ⇑? p) = a ⇑? (⇑ p).
Proof. intros [ | | | ]; reflexivity. Qed.

(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc-> Act -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P},
    lts (c ? P) (ActIn (c ⋉ v)) (P [⋅; v ..])
| lts_output : forall {c v P},
    lts (c ! v • P) (FreeOut (c ⋉ v)) P

(*The actions Tau*)
| lts_tau : forall {P},
    lts (t • P) τ P
| lts_recursion : forall {P},
    lts (rec P) τ (P [(rec P) ..; ⋅])
| lts_ifOne : forall {p q E}, Eval_Eq E = Some true -> 
    lts (If E Then p Else q) τ p
| lts_ifZero : forall {p q E}, Eval_Eq E = Some false -> 
    lts (If E Then p Else q) τ q

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 (FreeOut (c ⋉ v)) p2 ->
    lts q1 (ActIn (c ⋉ v)) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 (FreeOut (c ⋉ v)) p2 ->
    lts q1 (ActIn (c ⋉ v)) q2 ->
    lts (q1 ‖ p1) τ (q2 ‖ p2)

(* Scoped rules *)
| lts_close_l : forall {c p1 p2 q1 q2},
    lts p1 (BoundOut c) p2 ->      (* this term is an "open" term, (see the lts_open rule) *)
    lts (⇑ q1) (ActIn (⇑ c ⋉ 0)) q2 ->  (* while this one is a "closed" term *)
    lts (p1 ‖ q1) τ (ν (p2 ‖ q2))   (* so whe should shift q2 here. This corresponds to cgr_scope (scope extrusion) *)
| lts_close_r : forall {c p1 p2 q1 q2},
    lts q1 (BoundOut c) q2 ->
    lts (⇑ p1) (ActIn (⇑ c ⋉ 0)) p2 ->
    lts (p1 ‖ q1) τ (ν (p2 ‖ q2))
| lts_res : forall {p q α},
    lts p (⇑ α) q ->
    lts (ν p) α (ν (α ?↔ q ))
                      (* only α needs to shift here!! (both chan and value).
                         as a consequence, the channel in α can never be 0 (giving the condition in paper)
                         as in onther places: we started with an "open" value, that's why we add a flat ν *)
| lts_open : forall {c p1 p2}, (** remark: we are adding a ν but we are not shifting. this corresponds to the intuition in momigliano&cecilia that free rules handle open terms *)
    lts p1 (FreeOut ((⇑ c) ⋉ (var_Data 0))) p2 ->   (** condition: (⇑ c must not be 0 ! *)
    lts (ν p1) (BoundOut c) p2                      (* this should happen only when v = 0 *)
                                                    (* note that p2 is now an open term. its scope is going to be closed in the close rule *)

| lts_parL : forall {α} {p1 p2 q q' : proc},
    lts p1 α p2 ->
    q' = (if is_bound_out α then (⇑ q) else q) ->
    lts (p1 ‖ q) α (p2 ‖ q')
| lts_parR : forall {α} {p p' q1 q2 : proc}, 
    lts q1 α q2 ->
    p' = (if is_bound_out α then (⇑ p) else p) ->
    lts (p ‖ q1) α (p' ‖ q2)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q -> 
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q -> 
    lts (p1 + p2) α q
.

(* observations: a closed term does no visible actions (only τ) *)


Lemma res_not_bound : forall p α q,
  is_bound_out α = false ->
  lts p (⇑ α) q ->
  lts (ν p) α (ν q).
Proof.
intros. apply lts_res in H0. rewrite H in H0. assumption.
Qed.

Lemma res_bound : forall p α q,
  is_bound_out α = true ->
  lts p (⇑ α) q ->
  lts (ν p) α (ν q ⟨swap⟩).
Proof.
intros. apply lts_res in H0. rewrite H in H0. assumption.
Qed.

Lemma parR_bound : forall p α q1 q2,
  is_bound_out α = true ->
  lts q1 α q2 ->
  lts (p ‖ q1) α (⇑ p ‖ q2).
Proof.
intros. eapply lts_parR in H0. exact H0. now rewrite H.
Qed.

Lemma parR_not_bound : forall p α q1 q2,
  is_bound_out α = false ->
  lts q1 α q2 ->
  lts (p ‖ q1) α (p ‖ q2).
Proof.
intros. eapply lts_parR in H0. exact H0. now rewrite H.
Qed.

#[global] Hint Constructors lts:lts.
#[global] Hint Resolve res_not_bound res_bound parR_bound parR_not_bound : lts.
