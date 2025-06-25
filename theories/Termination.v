(* Lemmas and tactics to help prove termination and related properties *)

From Must Require Import TransitionSystems Lift.
From stdpp Require Import strings sets gmap base.

(* Tactic that looks for lts/lts_step assumptions and inverts them to
  learn about the shape of the conclusion *)
Ltac lts_inversion lts :=
try match goal with
| H : lts_step ?p ?a ?q |- _ =>
  solve[inversion H; subst; discriminate || tauto]
| H : lts ?p ?a ?q |- _ => inversion H; subst; discriminate || tauto
 end;
match goal with
| H : lts_step ?p ?a ?q |- _ => inversion H; subst; clear H
| H : lts ?p ?a ?q |- _ => inversion H; subst; clear H
 end.

(* A tactic to try and prove termination.
  Should be complete in the absence of recusion. *)
Ltac step_tac lts := 
try match goal with |H : {[+ ?a +]} ⊎ ?m = ∅ |- _ =>
  now (apply Lift.neq_multi_nil in H) end; 
try discriminate; constructor; intros; repeat lts_inversion lts.

Ltac term_tac lts := repeat (step_tac lts).


(* Maybe move to a separate file *)
(* Simulation *)
CoInductive similar `{@Lts A L H} `{@Lts B L H}  (a : A) (b : B) : Prop :=
| smi_step : (forall (α : Act L) a', a ⟶{α} a' -> exists b', b ⟶{α} b' /\ similar a' b') -> similar a b.
Infix "≲" := (similar) (at level 20).


Section Similarity.

(* Similarity preserves termination *)
Lemma similar_terminate `{@Lts A L H} `{@Lts B L H} (a : A) (b : B) :
  b ≲ a -> a ⤓ -> b ⤓.
Proof.
intros Hs Ht. revert b Hs. induction Ht as [a Ht Hi].
constructor. intros q Hq. destruct Hs as [Hs].
destruct (Hs τ q Hq) as (a' & Ha' & Hs').
eapply Hi; eassumption.
Qed.

End Similarity.

Section TerminateWith.

Context `{Lts A L}.

(* Generalisation of termination where each tau-accessible external action
  must satisfy some property *)
Reserved Notation "p ⤓_ Q " (at level 50).
Inductive terminate_with (Q : ExtAct L -> Prop) (p : A) : Prop :=
    twstep : (forall μ q, p ⟶[μ] q -> Q μ) -> 
             (forall q : A, p ⟶ q -> q ⤓_ Q) -> p ⤓_ Q
where "p ⤓_ Q" := (terminate_with Q p).

(* Termination is termination_with the trivial property on external actions *)
Lemma terminate_with_True p : p ⤓ -> p ⤓_ (fun _ => True).
Proof. intro Ht; induction Ht; constructor; auto. Qed.

Lemma terminate_with_terminate Q p : p ⤓_ Q -> p ⤓.
Proof. intro Ht; induction Ht; constructor; auto. Qed.

Notation "p '⤓_' Q" := (terminate_with Q p).

End TerminateWith.

Section ParallelTermination.

Context `{LA : @Lts A L HL}.
Context `{LB : @Lts B L HL}.

Local Instance LAB : Lts (A * B) L := parallel_lts LA LB.

(* The parallel composition of two states that may never interact *)
Lemma parallel_termination_with P Q (p : A) (q : B) :
  (forall μ μ', P μ -> Q μ' -> not (ext_act_match μ μ')) ->
  terminate_with P p ->
  terminate_with Q q ->
    terminate (p, q).
Proof.
intros Hm Hp Hq. revert q Hq.
induction Hp as [p He Ht Hi]. intros q Hq.
induction Hq as [q He' Ht' Hi'].
constructor.
intros (r & s) Hrs. lts_inversion idtac.
- now apply Hi.
- now apply Hi'. (* right tau *) 
- (* communication is impossible *)
  destruct α1 as [μ1|]; [|simpl in *; tauto].
  destruct α2 as [μ2|]; [|simpl in *; tauto].
  exfalso; eapply Hm.
  + eapply He. eassumption.
  + eapply He'. eassumption.
  + trivial.
Qed.

End ParallelTermination.