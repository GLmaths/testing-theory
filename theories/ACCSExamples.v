From Must Require Import ACCSInstance TransitionSystems Coin.
From stdpp Require Import strings sets gmap base.
From Coq Require Import Relations.

(* Tactic that looks for lts/lts_step assumptions and inverts them to
  learn about the shape of the conclusion *)
Ltac lts_inversion :=
repeat match goal with
| H : lts_step ?p ?a ?q |- _ => inversion H; subst; clear H
| H : lts ?p ?a ?q |- _ => inversion H; subst; clear H
 end.

Lemma parallel_output_terminate M a b : (!a ∥ !b ▷ M) ⤓.
Proof.
constructor. intros (p, M') Hl. inversion Hl; subst.
- lts_inversion. discriminate.
- decompose record Hl. lts_inversion.
Qed.

(* A tactic to try and prove termination *)
Ltac term_tac := repeat(constructor; intros; lts_inversion).

Example q_terminate : forall M, (!"a" ∥ (τ⋅ !"b" ⊕  τ⋅ !"c") ▷ M) ⤓.
Proof. intro M. term_tac. Qed.

Lemma choice_copre_l p q: forall (M : mb name) X,
  {[τ⋅ p ⊕ τ⋅ q ▷ M]} ∪ X ⩽ p ▷ M.
Proof.
intros M X. eapply c_tau.
- apply coin_union, coin_refl.
- constructor. apply lts_choiceL. constructor.
Qed.

Lemma choice_copre_r p q: forall (M : mb name) X,
  {[τ⋅ p ⊕ τ⋅ q ▷ M]} ∪ X ⩽ q ▷ M.
Proof.
intros M X. eapply c_tau.
- apply coin_union, coin_refl.
- constructor. apply lts_choiceR. constructor.
Qed.

(* faster than set set_solver *)
Ltac set_tac :=
(apply elem_of_union_r; set_tac) ||
(apply elem_of_union_l; set_tac) ||
now apply elem_of_singleton_2.

Lemma choice_copre_rev p q: forall M X,
  {[ (p ▷ M); (q ▷ M) ]} ∪ X ⩽ τ⋅ p ⊕ τ⋅ q ▷ M.
Proof.
cofix hco.
intros. split.
- clear hco. intros (q', M') l. 
  inversion_clear l.
  + lts_inversion; apply coin_elem_of; set_tac.
  + lts_inversion.
- intros Ht Hs.
  exfalso. eapply (lts_stable_spec2 (τ⋅ p ⊕ τ⋅ q ▷ M)).
  eexists. eapply lts_fw_p, lts_choiceL, lts_tau. assumption.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + lts_inversion.
  + rewrite (union_difference_L {[p ▷ m; q ▷ m ]} ps'). apply hco.
    clear hco.
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ {[+ a +]} ⊎ m). set_tac.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
    * apply Hw with (q ▷ {[+ a +]} ⊎ m). set_tac.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
  + rewrite (union_difference_L {[p ▷ {[+ a +]} ⊎ M; q ▷ {[+ a +]} ⊎ M]} ps'). apply hco.
    clear hco.
    intros p' mem%elem_of_union.
    destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
    * apply Hw with (p ▷ M). set_tac.
      eapply wt_act. apply lts_fw_inp_mb. apply wt_nil.
    * eapply Hw with (q ▷ M). set_tac.
      eapply wt_act. eapply lts_fw_inp_mb. eapply wt_nil.
- clear hco. intros Ht. constructor. intros (q', M') l.
  inversion l; subst; lts_inversion; apply Ht; set_tac.
Qed.

(* TODO: avoid using h2 *)
Example code_hoisting_outputs : forall (M : mb name) X,
    {[ τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ M ]} ∪ X
      ⩽ !"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M.
Proof.
cofix hco.
intros M X. split.
- intros q l. lts_inversion.
  + apply choice_copre_l.
  + apply choice_copre_r.
- intros. exfalso.
  eapply (lts_stable_spec2 (!"a" ∥ (τ⋅ !"b" ⊕ τ⋅ !"c") ▷ M)); eauto.
  exists (!"a" ∥ !"b" ▷ M). eapply lts_fw_p, lts_parR, lts_choiceL, lts_tau.
- intros μ q' ps' H0 Hμ Hw. inversion Hμ; subst.
  + lts_inversion.
  (* h2 : pas beau ! adhoc ; ACCS *)
    eapply h2.
    -- etrans. eapply t_step. eapply cgr_par_nil_rev.
       etrans. eapply t_step. eapply cgr_par_com. reflexivity.
    -- eapply (h2 (τ⋅ (pr_nil ∥ !"b") ⊕ τ⋅ (pr_nil ∥ !"c"))).
      ++ symmetry.
         etrans. eapply t_step. eapply cgr_choice.
         eapply cgr_tau. eapply cgr_par_nil_rev.
         eapply cgr_tau. eapply cgr_par_nil_rev.
         etrans. eapply t_step. eapply cgr_choice.
         eapply cgr_tau. eapply cgr_par_com.
         eapply cgr_tau. eapply cgr_par_com. reflexivity.
      ++ assert (Hi : {[ (pr_nil ∥ !"b" ▷ M); (pr_nil ∥ !"c" ▷ M) ]} ⊆ ps'). {
          intros x mem%elem_of_union.
           destruct mem as [hl%elem_of_singleton | hr%elem_of_singleton]; subst.
           eapply Hw. eapply elem_of_union. left. now eapply elem_of_singleton.
           eapply wt_tau. eapply lts_fw_p. eapply lts_choiceL, lts_tau.
           eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output. eapply wt_nil.
           eapply Hw. eapply elem_of_union. left. now eapply elem_of_singleton.
           eapply wt_tau. eapply lts_fw_p. eapply lts_choiceR, lts_tau.
           eapply wt_act. eapply lts_fw_p. eapply lts_parL, lts_output. eapply wt_nil.
         }
         eapply union_difference_L in Hi.
         rewrite Hi. eapply choice_copre_rev.
  + assert (Hin : τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ m ∈ ps').
    * eapply Hw.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_out_mb m). eapply wt_nil.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply hco.
  + assert (Hin : τ⋅ (!"a" ∥ !"b") ⊕ τ⋅ (!"a" ∥ !"c") ▷ {[+ a +]} ⊎ M ∈ ps').
    * eapply Hw.
      eapply elem_of_union. left.
      eapply elem_of_singleton. reflexivity.
      eapply wt_act. eapply (lts_fw_inp_mb M). eapply wt_nil.
    * eapply union_difference_singleton_L in Hin.
      rewrite Hin. eapply hco.
- intros. eapply q_terminate.
Qed.

(* TODO: generalisation
Example code_hoisting_gen a b c: forall (M : mb name) X,
    {[ τ⋅ (a ∥ b) ⊕ τ⋅ (a ∥ c) ▷ M ]} ∪ X
      ⩽ a ∥ (τ⋅ b ⊕ τ⋅ c) ▷ M.
*)
