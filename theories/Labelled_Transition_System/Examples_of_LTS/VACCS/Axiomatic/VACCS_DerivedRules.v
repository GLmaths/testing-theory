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


(** * Rules that are no longer rules

    [ax_input_drop] (drop a guard whose continuation is [Bad]) and
    [ax_restrict] (restrict a stable sum, certified by [BadK]) used to be
    rules of the system.  Completeness ([VACCS_Matching.completeness_ax])
    does not use them, so they are removed from [ax_pre] and recovered
    here as **corollaries**: their semantic justification is proved
    ([VACCS_Absorb.must_i_input_drop_bad], [must_i_restrict_badk]) and
    completeness turns it into a derivation.  The price is a [gStatic]
    hypothesis, completeness holding on the [Static] fragment.

    The laws built on them follow, with the same statements plus that
    hypothesis. *)

From Stdlib Require Import List Lia.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import base sets gmap gmultiset.
From TestingTheory Require Import MultisetLTSConstruction VACCS_Forwarder.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Precongruence VACCS_Residues VACCS_Expansion VACCS_ReadySet VACCS_Cond2
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx VACCS_Canonical
  VACCS_ResNormalize VACCS_Shift VACCS_NormalForm Termination DefinitionCI
  SetLTSConstruction FiniteImageLTS Lts_Finite_Output_Chain VACCS_Matching.

Section VACCS_DerivedRules.

Context `{VP : VACCS_Parameters}.

Lemma ax_input_drop : forall (c : ChannelData) (P : proc) (G : gproc),
  gStatic ((c ? P) + G) ->
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v P)) ->
  (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c P G HS HP. apply completeness_ax.
  - apply static_g. exact HS.
  - apply static_g. inversion HS; assumption.
  - apply must_i_input_drop_bad. exact HP.
Qed.

Lemma ax_restrict : forall (M M' : gproc),
  gStatic M -> gStatic M' ->
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall p, ~ lts (g M) τ p) ->
  BadK (fun _ => False) (offers M') (g M) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g M').
Proof.
  intros M M' HM HM' Hsub Hst Hk. apply completeness_ax.
  - apply static_g. exact HM.
  - apply static_g. exact HM'.
  - apply must_i_restrict_badk; assumption.
Qed.

(** ** The copycat, the responder and the swallow *)

Lemma ax_ccat_l : forall c, (ccat c) ᴠᴀᴄᴄꜱ⊑ₐₓ (g 𝟘).
Proof.
  intro c. apply completeness_ax; [ unfold ccat; repeat constructor | repeat constructor | ].
  apply must_i_ccat_l.
Qed.

Lemma ax_resp : forall (a : Channel) (V : ValueData),
  (resp a V) ᴠᴀᴄᴄꜱ⊑ₐₓ (ccat (cst a)).
Proof.
  intros a V. apply completeness_ax;
    [ unfold resp; repeat constructor | unfold ccat; repeat constructor | ].
  apply must_i_resp_below_ccat.
Qed.

Lemma ax_swallow : forall (c : ChannelData) (G : gproc),
  gStatic G -> (g ((c ? (g 𝟘)) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c G HG. apply ax_input_drop; [ repeat constructor; exact HG | ].
  intro v. simpl. apply bad_nil_any.
Qed.

(** A guard may be dropped as soon as its continuation emits only on the
    guard's own channel — the sink ([ochans P = []]) and the copycat
    ([ochans P ⊆ {c}]) are both instances. *)

Lemma ax_drop_ochans : forall (c : ChannelData) (P : proc) (G : gproc),
  Static P -> gStatic G -> (forall d, In d (ochans P) -> d = c) ->
  (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c P G HSt HG Hsub. apply ax_input_drop; [ repeat constructor; assumption | ].
  intro v. apply ochans_sub_Bad.
  - apply Static_subst. exact HSt.
  - intros d Hd. rewrite ochans_subst in Hd. apply Hsub. exact Hd.
Qed.

Corollary ax_drop_no_output : forall (c : ChannelData) (P : proc) (G : gproc),
  Static P -> gStatic G -> ochans P = [] -> (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c P G HSt HG Hoc. apply ax_drop_ochans; [ exact HSt | exact HG | ].
  intros d Hd. rewrite Hoc in Hd. contradiction.
Qed.

Example ax_drop_nested_sink : forall (c d : ChannelData) (G : gproc),
  gStatic G -> (g ((c ? ((g (d ? ((g 𝟘) : proc))) : proc)) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c d G HG. apply ax_drop_no_output; [ repeat constructor | exact HG | reflexivity ].
Qed.

Example ax_drop_copycat : forall (c : ChannelData) (G : gproc),
  gStatic G -> (g ((c ? (((c ! (bvar 0) • 𝟘)) : proc)) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c G HG. apply ax_drop_ochans; [ repeat constructor | exact HG | ].
  intros d Hd. simpl in Hd. destruct Hd as [Hd|[]]. symmetry. exact Hd.
Qed.

(** ** Dropping up to a rewrite of the continuation *)

Lemma ax_input_drop_upto :
  forall (c : ChannelData) (P Q : proc) (G : gproc),
  gStatic ((c ? Q) + G) ->
  (forall v : ValueData, (subst_in_proc 0 v P) ᴠᴀᴄᴄꜱ⊑ₐₓ (subst_in_proc 0 v Q)) ->
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v Q)) ->
  (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c P Q G HS Hpq HQ.
  eapply ax_trans; [ apply ax_choice_input with (Q := Q); exact Hpq | ].
  apply ax_input_drop; [ exact HS | exact HQ ].
Qed.

Lemma ax_input_drop_int_l :
  forall (c : ChannelData) (A B : proc) (G : gproc),
  gStatic ((c ? (g ((𝛕 • A) + (𝛕 • B)))) + G) ->
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v A)) ->
  (g ((c ? (g ((𝛕 • A) + (𝛕 • B)))) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c A B G HS HA. apply ax_input_drop; [ exact HS | ]. intro v. simpl.
  eapply bad_step; [ apply lts_choiceL; apply lts_tau | apply HA ].
Qed.

Lemma ax_input_drop_int_r :
  forall (c : ChannelData) (A B : proc) (G : gproc),
  gStatic ((c ? (g ((𝛕 • A) + (𝛕 • B)))) + G) ->
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v B)) ->
  (g ((c ? (g ((𝛕 • A) + (𝛕 • B)))) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g G).
Proof.
  intros c A B G HS HB. apply ax_input_drop; [ exact HS | ]. intro v. simpl.
  eapply bad_step; [ apply lts_choiceR; apply lts_tau | apply HB ].
Qed.

(** ** Peeling mute summands, and dropping to [𝟘] *)

Lemma ax_rebuild_drop_ochans : forall (l r : list gproc),
  Forall gStatic l -> Forall gStatic r -> Forall DropOk l ->
  ((g (rebuild (l ++ r))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (rebuild r)) : proc).
Proof.
  induction l as [|aa l IH]; intros r HSt HStr HOk; simpl.
  - apply ax_refl.
  - inversion HSt as [|? ? HSt1 HSt2]; subst.
    inversion HOk as [|? ? HOk1 HOk2]; subst.
    assert (IHl : ((g (rebuild (l ++ r))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (rebuild r)) : proc))
      by (apply IH; assumption).
    destruct aa as [ | | c P | P | A B ]; simpl in HOk1.
    + eapply ax_trans; [ apply ax_success_l | ].
      eapply ax_trans; [ apply ax_cgr; apply cgr_nil_choice_l | ]. exact IHl.
    + eapply ax_trans; [ apply ax_cgr; apply cgr_nil_choice_l | ]. exact IHl.
    + eapply ax_trans; [ | exact IHl ].
      apply ax_drop_ochans;
        [ inversion HSt1; assumption
        | apply rebuild_gStatic; apply Forall_app; split; assumption
        | exact HOk1 ].
    + contradiction.
    + contradiction.
Qed.


Theorem ax_gsum_drop_ochans : forall (M : gproc) (l r : list gproc),
  gStatic M -> Permutation (summands M) (l ++ r) -> Forall DropOk l ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (rebuild r)) : proc).
Proof.
  intros M l r HM Hperm HOk.
  assert (HSt : Forall gStatic (l ++ r))
    by (apply perm_summands_gStatic with M; assumption).
  apply Forall_app in HSt as (HSt1 & HSt2).
  eapply ax_trans; [ apply ax_cgr | ].
  - transitivity (g (rebuild (summands M))); [ apply summands_cgr | ].
    apply (rebuild_perm (summands M) (l ++ r)). exact Hperm.
  - apply ax_rebuild_drop_ochans; assumption.
Qed.


Lemma ax_copycats_below_nil : forall M,
  gStatic M -> gCopycats M -> ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g 𝟘) : proc).
Proof.
  intros M HM HC.
  apply (ax_gsum_drop_ochans M (summands M) []).
  - exact HM.
  - rewrite app_nil_r. reflexivity.
  - apply gCopycats_DropOk. exact HC.
Qed.


Corollary ax_gsum_below_nil : forall (M : gproc),
  gStatic M -> gStable M -> ochans ((g M) : proc) = [] ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (𝟘 : gproc)) : proc).
Proof.
  intros M HM HSb HOc.
  apply (ax_gsum_drop_ochans M (summands M) []).
  - exact HM.
  - rewrite app_nil_r. reflexivity.
  - assert (HLf := summands_leaves M).
    assert (HSb' := gStable_summands M HSb).
    assert (HOc' := gochans_summands M HOc).
    rewrite Forall_forall in HLf, HSb', HOc' |- *.
    intros aa Hin. apply DropOk_of_mute; auto.
Qed.


Theorem ax_below_nil_noresd : forall (p : proc),
  Static p -> NoResD p -> ochans p = [] ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (𝟘 : gproc)) : proc).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hst Hnr Hoc. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - (* parallel: [ax_par], then [𝟘 ‖ 𝟘 ≡* 𝟘] *)
    inversion Hst; subst. simpl in Hnr, Hoc.
    destruct Hnr as (Hn1 & Hn2). apply app_eq_nil in Hoc as (Ho1 & Ho2).
    eapply ax_trans; [ apply ax_par | ].
    + apply (IHp p1 ltac:(simpl; lia)); assumption.
    + apply (IHp p2 ltac:(simpl; lia)); assumption.
    + apply ax_cgr. apply cgr_par_nil.
  - inversion Hst.
  - inversion Hst.
  - (* conditional: [Eval_Eq 0] never fails, so [≡*] one branch *)
    inversion Hst; subst. simpl in Hnr, Hoc.
    destruct Hnr as (Hn1 & Hn2). apply app_eq_nil in Hoc as (Ho1 & Ho2).
    destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + eapply ax_trans; [ apply ax_cgr; apply cgr_if_true; exact HE | ].
      apply (IHp p1 ltac:(simpl; lia)); assumption.
    + eapply ax_trans; [ apply ax_cgr; apply cgr_if_false; exact HE | ].
      apply (IHp p2 ltac:(simpl; lia)); assumption.
  - (* a message is excluded by the criterion itself *)
    simpl in Hoc. discriminate Hoc.
  - (* a restriction is excluded by [NoResD] — see the header *)
    simpl in Hnr. contradiction.
  - (* a guarded sum: stable, or peel its own [τ] *)
    destruct (lts_dec ((g M) : proc) τ) as [Hno|(X & HX)].
    + apply ax_gsum_below_nil; [ inversion Hst; assumption | | exact Hoc ].
      apply gStable_iff. apply no_lts_stable. exact Hno.
    + eapply ax_trans; [ apply ax_tau_step; exact HX | ].
      apply (IHp X).
      * unfold ltof. eapply Static_lts_decrease; [ exact Hst | exact HX ].
      * eapply Static_preserved_by_lts; [ exact Hst | exact HX ].
      * eapply noresd_tau_target; [ exact Hnr | exact HX ].
      * assert (Hsub := lts_ochans_target _ _ _ Hst HX).
        destruct (ochans X) as [|d l0] eqn:E; [ reflexivity | exfalso ].
        assert (Hin : In d (ochans ((g M) : proc)))
          by (apply Hsub; left; reflexivity).
        rewrite Hoc in Hin. exact Hin.
Qed.


Theorem ax_below_nil_of_mute_reduct : forall (p x : proc),
  Static p -> NoResD p -> p ⟹[[]] x -> ochans x = [] ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (𝟘 : gproc)) : proc).
Proof.
  intros p x Hst Hnr Hw Hoc.
  eapply ax_trans; [ apply ax_tau_run; exact Hw | ].
  apply ax_below_nil_noresd.
  - eapply Static_preserved_by_wt; [ exact Hst | exact Hw ].
  - eapply noresd_wt_target; [ exact Hst | exact Hnr | exact Hw ].
  - exact Hoc.
Qed.


Theorem residue_instance_derivable : forall (c : ChannelData) (v : ValueData),
     (exists z, lts ((c ! v • 𝟘) ‖ ccat c) τ z)
  /\ ochans (ccat c) <> []
  /\ (forall z, ~ lts (msgs [(c ▷ v)]) τ z)
  /\ ((c ! v • 𝟘) ‖ ccat c) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [(c ▷ v)])
  /\ ((c ! v • 𝟘) ‖ ccat c) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs [(c ▷ v)]).
Proof.
  intros c v. split; [ | split; [ | split; [ | split ]]].
  - unfold ccat. eexists. eapply lts_comL; [ apply lts_output | apply lts_input ].
  - simpl. discriminate.
  - intros z Hz. simpl in Hz.
    inversion Hz; subst; try (inversion H3; fail); try (inversion H4; fail);
      inversion H2.
  - assert (Hc : ((c ! v • 𝟘) : proc) ≡* (msgs [(c ▷ v)]))
      by (simpl; apply cgr_symm; apply cgr_par_nil).
    intros t Ht.
    apply (proj2 (must_i_cgr _ _ Hc)).
    apply (proj2 (ccat_delivery_equiv c v)). exact Ht.
  - eapply ax_trans.
    + apply (ax_par (c ! v • 𝟘) (c ! v • 𝟘) (ccat c) ((g (𝟘 : gproc)) : proc));
        [ apply ax_refl | apply ax_ccat_l ].
    + apply ax_cgr. simpl. apply cgr_refl.
Qed.



End VACCS_DerivedRules.
