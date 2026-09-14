(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)


(** * Below a τ-stable guarded sum

    A guarded sum [g M] with no [τ] passes a client exactly when the
    client can move on its own, or emits on a channel [M] offers — and
    then survives each of [M]'s input continuations.  So [p] is below
    [g M] as soon as

    - [p], holding each received message, is below the corresponding
      input continuation (the [com] field), and
    - [p] fails every τ-stuck, non-good client whose pending messages
      all sit on channels [M] does not offer (the [ex] field).

    The second condition is stated here without clients: handed any bag
    of messages on channels [M] does not offer, [p] can settle into a
    stable state that emits only on the bag's own channels
    ([Settles]).  [must_i_glb_stable] proves that this suffices: a
    τ-stuck client strips into [msgs l ‖ t0] with [t0] mute
    ([strip_outputs_all]), the bag moves to the server side
    ([must_msgs_swap], [msgs_buffer_iff]), and the settled state and
    [t0] are then stuck together ([settles_fails_stuck]). *)

From Stdlib Require Import List PeanoNat Lia.
From stdpp Require Import base sets gmap gmultiset.
From TestingTheory Require Import Lts_Finite_Output_Chain.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence MultisetLTSConstruction ForwarderConstruction
  Lts_OBA Lts_FW Lts_OBA_FB VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Precongruence VACCS_Expansion VACCS_Forwarder VACCS_Cond2 VACCS_Absorb.

Section VACCS_GlbStable.

Context `{VP : VACCS_Parameters}.

(** A client is its pending messages beside a mute residue. *)
Lemma strip_outputs : forall n (t : proc),
  (gmultiset_size (lts_oba_mo t : gmultiset (ExtAct TypeOfActions)) <= n)%nat ->
  exists (l : list TypeOfActions) t0, t ≡* (msgs l ‖ t0) /\
    (forall a z, ~ lts t0 (ActExt (ActOut a)) z).
Proof.
  induction n as [|n IH]; intros t Hs.
  - exists [], t. split.
    + etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
    + intros a z Hl.
      assert (Hin : ActOut a ∈ lts_oba_mo t).
      { eapply lts_oba_mo_spec_bis1; [ | exact Hl ].
        unfold non_blocking. simpl. unfold non_blocking_output. exists a. reflexivity. }
      assert (Hz : gmultiset_size (lts_oba_mo t) = 0) by lia.
      apply gmultiset_size_empty_inv in Hz. rewrite Hz in Hin. set_solver.
  - destruct (gmultiset_choose_or_empty (lts_oba_mo t)) as [ (η & Hη) | E ].
    + destruct (lts_oba_mo_spec_bis2 t η Hη) as (t' & Hnb & Hl).
      destruct Hnb as (a & ->).
      assert (Hnb : non_blocking (ActOut a)).
      { unfold non_blocking. simpl. unfold non_blocking_output. exists a. reflexivity. }
      assert (Hsz := lts_oba_mo_spec2 t (ActOut a) t' Hnb Hl).
      assert (E : gmultiset_size (lts_oba_mo t) = S (gmultiset_size (lts_oba_mo t'))).
      { pose proof (gmultiset_size_disj_union ({[+ ActOut a +]} : gmultiset (ExtAct TypeOfActions))
                      (lts_oba_mo t')) as HH.
        pose proof (gmultiset_size_singleton (ActOut a : ExtAct TypeOfActions)) as HS.
        rewrite Hsz. etransitivity; [ exact HH | ]. unfold base.size in HS.
        exact (f_equal (fun k => (k + gmultiset_size (lts_oba_mo t'))%nat) HS). }
      assert (Hs' : (gmultiset_size (lts_oba_mo t') <= n)%nat) by lia.
      destruct (IH t' Hs') as (l' & t0 & Hc & Hno).
      destruct a as (c,v).
      exists ((c,v) :: l'), t0. split; [ | exact Hno ].
      eapply cgr_trans; [ apply TransitionShapeForOutputSimplified; exact Hl | ].
      simpl. eapply cgr_trans; [ apply cgr_fullpar; [ reflexivity | exact Hc ] | ].
      apply cgr_par_assoc_rev.
    + exists [], t. split.
      * etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
      * intros a z Hl.
        assert (Hin : ActOut a ∈ lts_oba_mo t).
        { eapply lts_oba_mo_spec_bis1; [ | exact Hl ].
          unfold non_blocking. simpl. unfold non_blocking_output. exists a. reflexivity. }
        rewrite E in Hin. set_solver.
Qed.

Lemma strip_outputs_all : forall (t : proc), exists (l : list TypeOfActions) t0,
  t ≡* (msgs l ‖ t0) /\ (forall a z, ~ lts t0 (ActExt (ActOut a)) z).
Proof. intro t. eapply strip_outputs. reflexivity. Qed.

(** A settled server and a mute client that refuses the settled
    server's channels are stuck together. *)
Lemma settles_fails_stuck : forall (p t0 : proc) (l : list TypeOfActions),
  (forall z, ~ lts t0 τ z) -> ~ good_VACCS t0 ->
  (forall a z, ~ lts t0 (ActExt (ActOut a)) z) ->
  (forall c v w z, In (c,v) l -> ~ lts t0 (ActExt (ActIn (c,w))) z) ->
  Settles (chans (bag l)) (p ▷ bag l) ->
  ~ ((p ▷ bag l) must_pass t0).
Proof.
  intros p t0 l Htau Hng Hout Hin (y & Hw & Hst & Hem) Hm.
  pose proof (must_preserved_by_weak_nil_srv _ _ _ Hm Hw) as Hy.
  destruct Hy as [Hg | Hnh Hex Hpt Het Hcom ].
  - exact (Hng Hg).
  - destruct Hex as (z & Hz). inversion Hz; subst.
    + eapply no_step_of_stable; [ exact Hst | eassumption ].
    + eapply Htau. eassumption.
    + destruct μ2 as [a|a].
      * destruct μ1 as [b|b]; simpl in eq; [ inversion eq | ].
        destruct b as (d,w). destruct a as (d',w'). inversion eq; subst.
        destruct (Hem d' w' _ l1) as (w0 & Hw0).
        apply bag_elem in Hw0. eapply (Hin d' w0 w'); eassumption.
      * eapply Hout. eassumption.
Qed.

Lemma cgr_lts_back : forall (t u z : proc) al, t ≡* u -> lts u al z -> exists r, lts t al r.
Proof.
  intros t u z al Hc Hl.
  destruct (Congruence_Respects_Transition t z al) as (r & Hr & _).
  { exists u. split; assumption. }
  exists r. exact Hr.
Qed.

Lemma msgs_emits_in : forall (l : list TypeOfActions) c v, In (c,v) l ->
  exists z, lts (msgs l) (ActExt (ActOut (c,v))) z.
Proof.
  induction l as [|(c0,v0) l IH]; intros c v Hin; simpl in Hin; [ contradiction | ].
  destruct Hin as [E|Hin].
  - injection E as -> ->. eexists. simpl. eapply lts_parL. apply lts_output.
  - destruct (IH c v Hin) as (z & Hz). eexists. simpl. eapply lts_parR. exact Hz.
Qed.

(** The whole bag can sit on either side of the barrier. *)
Lemma must_msgs_swap : forall (l : list TypeOfActions) (p e : proc),
  ((msgs l ‖ p) must_pass e) <-> (p must_pass (msgs l ‖ e)).
Proof.
  induction l as [|cv l IH]; intros p e; simpl.
  - split; intro Hm.
    + eapply must_eq_client; [ apply cgr_symm; apply cgr_nil_par_l | ].
      apply (proj2 (must_i_cgr _ _ (cgr_nil_par_l p))). exact Hm.
    + apply (proj1 (must_i_cgr _ _ (cgr_nil_par_l p))).
      eapply must_eq_client; [ apply cgr_nil_par_l | exact Hm ].
  - destruct cv as (c, v).
    assert (Hc : ((((c ! v • 𝟘) : proc) ‖ msgs l) ‖ p)
                   ≡* ((msgs l ‖ p) ‖ ((c ! v • 𝟘) : proc))).
    { etransitivity; [ apply cgr_par_assoc | apply cgr_par_com ]. }
    assert (Hd : (msgs l ‖ (((c ! v • 𝟘) : proc) ‖ e))
                   ≡* ((((c ! v • 𝟘) : proc) ‖ msgs l) ‖ e)).
    { etransitivity; [ apply cgr_par_assoc_rev | ].
      apply cgr_fullpar; [ apply cgr_par_com | reflexivity ]. }
    split; intro Hm.
    + assert (Hs : ((msgs l ‖ p) ‖ ((c ! v • 𝟘) : proc)) must_pass e)
        by (apply (proj2 (must_i_cgr _ _ Hc)); exact Hm).
      apply (proj1 (must_msg_swap c v (msgs l ‖ p) e)) in Hs.
      apply IH in Hs.
      eapply must_eq_client; [ exact Hd | exact Hs ].
    + assert (Hs : p must_pass (msgs l ‖ (((c ! v • 𝟘) : proc) ‖ e)))
        by (eapply must_eq_client; [ apply cgr_symm; exact Hd | exact Hm ]).
      apply IH in Hs.
      apply (proj2 (must_msg_swap c v (msgs l ‖ p) e)) in Hs.
      apply (proj1 (must_i_cgr _ _ Hc)). exact Hs.
Qed.

(** A τ-stuck client that [p] passes meets [M] on one of its channels. *)
Lemma stuck_client_meets : forall (p : proc) (M : gproc) (t : proc),
  (forall l : list TypeOfActions, (forall c v, In (c,v) l -> ~ offers M c) ->
     Settles (chans (bag l)) (p ▷ bag l)) ->
  p must_pass t -> ~ good_VACCS t -> (forall z, ~ lts t τ z) ->
  exists c v q r, lts t (ActExt (ActOut (c,v))) q /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) r.
Proof.
  intros p M t Hcert Hm Hng Hst.
  destruct (emits_in_set_dec (offers M) (offers_dec M) t)
    as [ (c & (w & r & Hr) & (v & q & Hq)) | Hnone ].
  - destruct (lts_in_value_swap _ _ _ Hr c w v eq_refl) as (r' & Hr').
    exists c, v, q, r'. split; assumption.
  - exfalso.
    destruct (strip_outputs_all t) as (l & t0 & Hc & Hno).
    assert (Hoff : forall c v, In (c,v) l -> ~ offers M c).
    { intros c v Hin Hoff. destruct (msgs_emits_in l c v Hin) as (z & Hz).
      assert (Hl : lts (msgs l ‖ t0) (ActExt (ActOut (c,v))) (z ‖ t0))
        by (apply lts_parL; exact Hz).
      destruct (cgr_lts_back _ _ _ _ Hc Hl) as (r & Hr).
      eapply (Hnone c Hoff). exists v, r. exact Hr. }
    assert (Ht0 : forall z, ~ lts t0 τ z).
    { intros z Hz. assert (Hl : lts (msgs l ‖ t0) τ (msgs l ‖ z)) by (apply lts_parR; exact Hz).
      destruct (cgr_lts_back _ _ _ _ Hc Hl) as (r & Hr). exact (Hst r Hr). }
    assert (Hg0 : ~ good_VACCS t0).
    { intro Hg. apply Hng. eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hc ].
      constructor. right. exact Hg. }
    assert (Hin0 : forall c v w z, In (c,v) l -> ~ lts t0 (ActExt (ActIn (c,w))) z).
    { intros c v w z Hin Hz.
      destruct (lts_in_value_swap _ _ _ Hz c w v eq_refl) as (z' & Hz').
      destruct (msgs_emits_in l c v Hin) as (y & Hy).
      assert (Hl : lts (msgs l ‖ t0) τ (y ‖ z')) by (eapply lts_comL; eassumption).
      destruct (cgr_lts_back _ _ _ _ Hc Hl) as (r & Hr). exact (Hst r Hr). }
    assert (Hm1 : p must_pass (msgs l ‖ t0)) by (eapply must_eq_client; [ exact Hc | exact Hm ]).
    apply must_msgs_swap in Hm1. apply msgs_buffer_iff in Hm1.
    eapply settles_fails_stuck;
      [ exact Ht0 | exact Hg0 | exact Hno | exact Hin0 | apply Hcert; exact Hoff | exact Hm1 ].
Qed.

Theorem must_i_glb_stable : forall (p : proc) (M : gproc),
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (forall l : list TypeOfActions, (forall c v, In (c,v) l -> ~ offers M c) ->
     Settles (chans (bag l)) (p ▷ bag l)) ->
  (forall c v Q', lts ((g M) : proc) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q') ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g M).
Proof.
  intros p M Hst Hcert Hin t Hm.
  remember p as p0 eqn:Ep. revert Ep.
  induction Hm as [ p1 t Hg | p1 t Hnh Hex Hpt IHpt Het IHet Hcom IHcom ]; intro Ep; subst p1.
  - apply m_now. exact Hg.
  - apply m_step.
    + exact Hnh.
    + destruct (lts_dec t τ) as [ Hno | (z & Hz) ].
      * assert (Hm0 : p must_pass t) by (apply m_step; assumption).
        destruct (stuck_client_meets p M t Hcert Hm0 Hnh Hno) as (c & v & q & r & Hq & Hr).
        exists (r ▷ q).
        eapply (ParSync (ActIn (c,v)) (ActOut (c,v))); [ reflexivity | exact Hr | exact Hq ].
      * exists ((g M : proc) ▷ z). apply ParRight. exact Hz.
    + intros p' Hp'. exfalso. exact (Hst p' Hp').
    + intros t' Ht'. exact (IHet t' Ht' Hcert Hin eq_refl).
    + intros p' t' mu1 mu2 Hdual Hp' Ht'.
      destruct mu1 as [ (c,v) | (c,v) ].
      * destruct mu2 as [ (d,w) | (d,w) ]; simpl in Hdual; [ inversion Hdual | ].
        inversion Hdual; subst.
        apply (Hin d w p' Hp').
        assert (H1 : p must_pass ((d ! w • 𝟘) ‖ t')).
        { eapply must_eq_client; [ apply TransitionShapeForOutputSimplified; exact Ht' | ].
          apply m_step; assumption. }
        apply must_msg_swap in H1.
        destruct (must_i_cgr (((d ! w • 𝟘) : proc) ‖ p) (p ‖ ((d ! w • 𝟘) : proc))
                    ltac:(apply cgr_par_com)) as [Ha Hb].
        first [ exact (Ha _ H1) | exact (Hb _ H1) ].
      * exfalso. eapply gsum_no_out. exact Hp'.
Qed.

End VACCS_GlbStable.
