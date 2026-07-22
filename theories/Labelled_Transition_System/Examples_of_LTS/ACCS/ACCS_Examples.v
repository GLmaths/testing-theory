(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Program Require Import Equality.
From Stdlib.Strings Require Import String.
From Stdlib Require Import Relations.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.
From Coinduction Require Import all.

From TestingTheory Require Import InputOutputActions ActTau Must VACCS_Must_Characterization
  gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction
  InteractionBetweenLts Testing_Predicate DefinitionAS VACCS VACCS_Good VACCS_Instance
  Convergence WeakTransitions Subset_Act MultisetLTSConstruction Termination
  ACCSInstance ACCS_Must_Characterization Coin_tower Simulation ForwarderConstruction
  SetLTSConstruction FiniteImageLTS Soundness.

(* Local Coercion in VACCS.v does not propagate across files; redeclared here. *)
Local Coercion bvar : nat >-> Data.
Local Coercion cst_channel : Channel >-> ChannelData.
Local Coercion cst_value : Value >-> ValueData.

Open Scope string_scope.

(** * Examples *)
(** ** ACCS *)
(** *** Applications *)

(** Small helpers on weak-transition sets, missing from FiniteImageLTS. *)

Lemma wt_set_from_pset_spec1_union_rev_l `{Countable P, gLts P A}
  (ps : gset P) s (qs qs' : gset P) :
  wt_set_from_pset_spec1 ps s (qs ∪ qs') -> wt_set_from_pset_spec1 ps s qs.
Proof.
  intros Hyp p mem. eapply Hyp. set_solver.
Qed.

Lemma wt_set_from_pset_spec1_union_rev_r `{Countable P, gLts P A}
  (ps : gset P) s (qs qs' : gset P) :
  wt_set_from_pset_spec1 ps s (qs ∪ qs') -> wt_set_from_pset_spec1 ps s qs'.
Proof.
  intros Hyp p mem. eapply Hyp. set_solver.
Qed.

(** The empty set is a top element for the co-inductive tower preorder. *)
Lemma empty_is_a_top_element
  `{gLtsP : @gLts P A EA, !FiniteImagegLts P A}
  `{gLtsT : @gLtsEq T A EA}
  `{AbsPT : @AbsAction P T FinA PreAct A EA Φ 𝝳P _ _} (X : gset P) :
  forall (PRE : Chain (copre_m)),
    elem PRE X ∅.
Proof.
  intros PRE. eapply (gfp_chain PRE). eapply eqx.
  eapply alt_set_empty.
Qed.

(* Parallel composition in ACCS is similar to the parallel composition of LTSs *)
Lemma accs_parallel_sim (p q : proc) :
  (p ‖ q) ≲ ((p, q) : proc * proc).
Proof.
revert p q. cofix hco. intros p q. constructor.
intros α r Hstep. inversion Hstep; subst.
- eexists (p2, q2); split.
  + eapply (ParSync (ActOut (c, v)) (ActIn (c, v))); simpl; eauto.
  + apply hco.
- eexists (q2, p2); split.
  + eapply (ParSync (ActIn (c, v)) (ActOut (c, v))); simpl; eauto.
  + apply hco.
- eexists (p2, q); split.
  + eapply ParLeft; eauto.
  + apply hco.
- eexists (p, q2); split.
  + eapply ParRight; eauto.
  + apply hco.
Qed.

(* Parallel composition in ACCS with forwarders is similar to the parallel
   composition of LTSs, with the forwarder component on the left (the only
   direction for which a [Prop_of_Inter] instance is available). *)
Lemma accs_fw_parallel_sim (p q : proc) (M : MO (ExtAct TypeOfActions)) :
  ((p ‖ q) ▷ M) ≲ (((q ▷ M), p) : (proc * MO (ExtAct TypeOfActions)) * proc).
Proof.
revert M p q. cofix hco. intros M p q. constructor.
intros α r Hstep. inversion Hstep; subst.
- inversion l; subst.
  + eexists ((q2 ▷ M), p2); split.
    * eapply (ParSync (ActIn (c, v)) (ActOut (c, v))); simpl; eauto.
      eapply ParLeft; eauto.
    * apply hco.
  + eexists ((p2 ▷ M), q2); split.
    * eapply (ParSync (ActOut (c, v)) (ActIn (c, v))); simpl; eauto.
      eapply ParLeft; eauto.
    * apply hco.
  + eexists ((q ▷ M), p2); split.
    * eapply ParRight; eauto.
    * apply hco.
  + eexists ((q2 ▷ M), p); split.
    * eapply ParLeft, ParLeft; eauto.
    * apply hco.
- inversion l; subst.
  + eexists ((q ▷ {[+ η +]} ⊎ M), p); split.
    * eapply ParLeft, ParRight. eapply lts_multiset_add; eauto.
    * apply hco.
  + eexists ((q ▷ b2), p); split.
    * eapply ParLeft, ParRight. eapply lts_multiset_minus; eauto.
    * apply hco.
- inversion l1; subst.
  + destruct eq as (duo & nb).
    eexists ((q ▷ b2), p2); split.
    * eapply (ParSync μ2 μ1); simpl; eauto.
      symmetry. exact duo.
      eapply ParRight; eauto.
    * apply hco.
  + eexists ((q2 ▷ b2), p); split.
    * eapply ParLeft. eapply (ParSync μ1 μ2); eauto.
    * apply hco.
Qed.

Lemma pr_nil_fw_similar (p : proc) (M : MO (ExtAct TypeOfActions)) :
  ((g 𝟘 ‖ p) ▷ M) ≲ (p ▷ M).
Proof.
revert p M. cofix hco. intros p M.
constructor. intros α r Hstep. inversion Hstep; subst.
- inversion l; subst.
  + inversion H1.
  + inversion H4.
  + inversion H3.
  + eexists; split. eapply ParLeft; eauto. apply hco.
- eexists; split. eapply ParRight; eauto. apply hco.
- inversion l1; subst.
  + inversion H3.
  + eexists; split. eapply ParSync; eauto. apply hco.
Qed.

Lemma parallel_output_mb_similar (c : Channel) (v : Value) :
  forall (q : proc) (M : MO (ExtAct TypeOfActions)),
  (((c ! v • 𝟘) ‖ q) ▷ M) ≲ (q ▷ {[+ ActOut (cst c, cst v) +]} ⊎ M).
Proof.
cofix hco. intros q M.
constructor. intros α r Hstep.
inversion Hstep; subst; clear Hstep.
- inversion l; subst.
  + inversion H1; subst.
    eexists (q2 ▷ M); split.
    * eapply (ParSync (ActIn (cst c, cst v)) (ActOut (cst c, cst v)));
        [ split; [simpl; eauto | eexists; eauto]
        | eauto
        | eapply lts_multiset_minus; eexists; eauto ].
    * eapply pr_nil_fw_similar.
  + inversion H4.
  + inversion H3; subst.
    eexists (q ▷ M); split.
    * eapply ParRight. eapply lts_multiset_minus. eexists; eauto.
    * eapply pr_nil_fw_similar.
  + eexists (q2 ▷ ({[+ ActOut (cst c, cst v) +]} ⊎ M)); split.
    * eapply ParLeft; eauto.
    * eapply hco.
- inversion l; subst.
  + eexists (q ▷ ({[+ ActOut (cst c, cst v) +]} ⊎ ({[+ η +]} ⊎ M))); split.
    * eapply ParRight.
      replace ({[+ ActOut (cst c, cst v) +]} ⊎ ({[+ η +]} ⊎ M))
        with ({[+ η +]} ⊎ ({[+ ActOut (cst c, cst v) +]} ⊎ M))
        by (clear hco; multiset_solver).
      eapply lts_multiset_add; eauto.
    * eapply hco.
  + eexists (q ▷ ({[+ ActOut (cst c, cst v) +]} ⊎ b2)); split.
    * eapply ParRight.
      replace ({[+ ActOut (cst c, cst v) +]} ⊎ ({[+ η +]} ⊎ b2))
        with ({[+ η +]} ⊎ ({[+ ActOut (cst c, cst v) +]} ⊎ b2))
        by (clear hco; multiset_solver).
      eapply lts_multiset_minus; eauto.
    * eapply hco.
- inversion l1; subst.
  + inversion H3; subst.
    destruct eq as (duo & nb).
    eapply simplify_match_output in duo. subst.
    destruct nb as (a & eq'). inversion eq'.
  + inversion l2; subst.
    * destruct eq as (duo' & nb').
      exfalso. eapply dual_blocks in duo; eauto.
    * eexists (q2 ▷ ({[+ ActOut (cst c, cst v) +]} ⊎ b2)); split.
      { eapply (ParSync μ1 μ2); eauto.
        replace ({[+ ActOut (cst c, cst v) +]} ⊎ ({[+ μ2 +]} ⊎ b2))
          with ({[+ μ2 +]} ⊎ ({[+ ActOut (cst c, cst v) +]} ⊎ b2))
          by (clear hco; multiset_solver).
        eapply lts_multiset_minus. destruct eq; eauto. }
      eapply hco.
Qed.

(** The co-inductive tower preorder is stable by union on the right.
    (This was left admitted (as [coin_union_left]) on the branch this file
    was imported from; proven here by tower induction + finite-set
    induction on the target set.) *)
Lemma coin_union_right `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m}
  : forall (X Y1 Y2 : gset P), elem PRE X Y1 -> elem PRE X Y2 -> elem PRE X (Y1 ∪ Y2).
Proof.
  apply tower; clear PRE.
  - intros S HS X Y1 Y2 h1 h2. intros R HR. eapply HS; eauto.
  - intros PRE CIH X Y1 Y2 h1 h2.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply CIH; eauto.
        destruct (h_x x) as (y & mem & hw); [set_solver|].
        apply elem_of_union in mem as [m1|m2].
        -- eapply h1.(c_tau_). intros z hz.
           apply elem_of_singleton_1 in hz; subst z. eauto.
        -- eapply h2.(c_tau_). intros z hz.
           apply elem_of_singleton_1 in hz; subst z. eauto.
    + intros hX q mem hq.
      apply elem_of_union in mem as [m1|m2].
      * eapply h1.(c_now_); eauto.
      * eapply h2.(c_now_); eauto.
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply CIH; eauto.
        destruct (h_x x) as (y & mem & hw); [set_solver|].
        apply elem_of_union in mem as [m1|m2].
        -- eapply h1.(c_step_); eauto. intros z hz.
           apply elem_of_singleton_1 in hz; subst z. eauto.
        -- eapply h2.(c_step_); eauto. intros z hz.
           apply elem_of_singleton_1 in hz; subst z. eauto.
    + intros hX. eapply termination_set_for_all. intros y mem.
      apply elem_of_union in mem as [m1|m2].
      * eapply termination_if_termination_set_helper.
        eapply h1.(c_cnv_); eauto. eauto.
      * eapply termination_if_termination_set_helper.
        eapply h2.(c_cnv_); eauto. eauto.
Qed.

(** τ-guarded internal choice is below each of its branches (plain processes). *)
Lemma choice_copre_l' (p q : proc) :
  forall (PRE : Chain (copre_m (P := proc) (Q := proc) (T := proc))),
    elem PRE {[g (𝛕 • p + 𝛕 • q)]} {[p]}.
Proof.
intros PRE. eapply (c_tau' (Y := {[g (𝛕 • p + 𝛕 • q)]})).
- eapply (gfp_bchain PRE). eapply eqx. eapply alt_set_singleton_iff.
  split; [intros s h; eauto | intros s q' h1 h2 h3; eauto 6].
- intros y hy. apply elem_of_singleton_1 in hy; subst y.
  exists (g (𝛕 • p + 𝛕 • q)). split; [apply elem_of_singleton_2; reflexivity|].
  eapply lts_to_wt_tau. apply lts_choiceL. constructor.
Qed.

Lemma choice_copre_r' (p q : proc) :
  forall (PRE : Chain (copre_m (P := proc) (Q := proc) (T := proc))),
    elem PRE {[g (𝛕 • p + 𝛕 • q)]} {[q]}.
Proof.
intros PRE. eapply (c_tau' (Y := {[g (𝛕 • p + 𝛕 • q)]})).
- eapply (gfp_bchain PRE). eapply eqx. eapply alt_set_singleton_iff.
  split; [intros s h; eauto | intros s q' h1 h2 h3; eauto 6].
- intros y hy. apply elem_of_singleton_1 in hy; subst y.
  exists (g (𝛕 • p + 𝛕 • q)). split; [apply elem_of_singleton_2; reflexivity|].
  eapply lts_to_wt_tau. apply lts_choiceR. constructor.
Qed.

(** Same, on forwarder states. *)
Lemma choice_copre_l (p q : proc) :
  forall (PRE : Chain (copre_m (P := proc * MO (ExtAct TypeOfActions))
                               (Q := proc * MO (ExtAct TypeOfActions))
                               (T := proc)))
    (M : MO (ExtAct TypeOfActions)),
    elem PRE {[(g (𝛕 • p + 𝛕 • q)) ▷ M]} {[p ▷ M]}.
Proof.
intros PRE M. eapply (c_tau' (Y := {[(g (𝛕 • p + 𝛕 • q)) ▷ M]})).
- eapply (gfp_bchain PRE). eapply eqx. eapply alt_set_singleton_iff.
  split; [intros s h; eauto | intros s q' h1 h2 h3; eauto 6].
- intros y hy. apply elem_of_singleton_1 in hy; subst y.
  exists ((g (𝛕 • p + 𝛕 • q)) ▷ M). split; [apply elem_of_singleton_2; reflexivity|].
  eapply lts_to_wt_tau. apply ParLeft, lts_choiceL. constructor.
Qed.

Lemma choice_copre_r (p q : proc) :
  forall (PRE : Chain (copre_m (P := proc * MO (ExtAct TypeOfActions))
                               (Q := proc * MO (ExtAct TypeOfActions))
                               (T := proc)))
    (M : MO (ExtAct TypeOfActions)),
    elem PRE {[(g (𝛕 • p + 𝛕 • q)) ▷ M]} {[q ▷ M]}.
Proof.
intros PRE M. eapply (c_tau' (Y := {[(g (𝛕 • p + 𝛕 • q)) ▷ M]})).
- eapply (gfp_bchain PRE). eapply eqx. eapply alt_set_singleton_iff.
  split; [intros s h; eauto | intros s q' h1 h2 h3; eauto 6].
- intros y hy. apply elem_of_singleton_1 in hy; subst y.
  exists ((g (𝛕 • p + 𝛕 • q)) ▷ M). split; [apply elem_of_singleton_2; reflexivity|].
  eapply lts_to_wt_tau. apply ParLeft, lts_choiceR. constructor.
Qed.

(** Inversion helpers for τ-guarded binary choice. *)

Lemma choice_tau_inv (p q t : proc) : (g (𝛕 • p + 𝛕 • q)) ⟶ t -> t = p \/ t = q.
Proof.
  intro Hstep. inversion Hstep; subst.
  - inversion H3; subst. eauto.
  - inversion H3; subst. eauto.
Qed.

Lemma choice_ext_inv (p q t : proc) μ : (g (𝛕 • p + 𝛕 • q)) ⟶[μ] t -> False.
Proof.
  intro Hstep. inversion Hstep; subst.
  - inversion H3.
  - inversion H3.
Qed.

Lemma choice_wt_nil_inv (p q : proc) y :
  (g (𝛕 • p + 𝛕 • q)) ⟹ y -> y = g (𝛕 • p + 𝛕 • q) \/ p ⟹ y \/ q ⟹ y.
Proof.
  intro Hw. inversion Hw; subst.
  - eauto.
  - eapply choice_tau_inv in l as [-> | ->]; eauto.
Qed.

Lemma choice_wt_act_inv (p q : proc) μ y :
  (g (𝛕 • p + 𝛕 • q)) ⟹{μ} y -> p ⟹{μ} y \/ q ⟹{μ} y.
Proof.
  intro Hw. inversion Hw; subst.
  - eapply choice_tau_inv in l as [-> | ->]; eauto.
  - exfalso. eapply choice_ext_inv; eauto.
Qed.

(** A singleton is below any of its weak τ-descendants. *)
Lemma coin_wt_nil_singleton `{@FiniteImagegLts P A H gLtsP}
  `{gLtsT : !gLtsEq T H}
  `{AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ }
  {PRE : Chain copre_m} (x y : P) :
  x ⟹ y -> elem PRE {[x]} {[y]}.
Proof.
  intro Hw. eapply (c_tau' (Y := {[x]})).
  - eapply (gfp_bchain PRE). eapply eqx. eapply alt_set_singleton_iff.
    split; [intros s h; eauto | intros s q' h1 h2 h3; eauto 6].
  - intros z hz. apply elem_of_singleton_1 in hz; subst z.
    exists x. split; [apply elem_of_singleton_2; reflexivity|]. exact Hw.
Qed.

(** τ-guarded internal choice is above the set of its branches. *)
Lemma choice_copre_rev' (p q : proc) :
  forall (PRE : Chain (copre_m (P := proc) (Q := proc) (T := proc))),
    elem PRE ({[ p; q ]}) {[ g (𝛕 • p + 𝛕 • q) ]}.
Proof.
  apply (tower (P := fun R => R ({[ p; q ]} : gset proc) {[ g (𝛕 • p + 𝛕 • q) ]})).
  - intros S HS R HR. eapply HS; eauto.
  - intros PRE CIH.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply choice_wt_nil_inv in hw as [-> | [hp | hq]].
        -- eapply CIH.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_l, elem_of_singleton_2; reflexivity.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_r, elem_of_singleton_2; reflexivity.
    + intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      eapply (lts_refuses_spec2 (g (𝛕 • p + 𝛕 • q)) τ);
        [exists p; apply lts_choiceL; constructor | exact hst].
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply choice_wt_act_inv in hw as [hp | hq].
        -- eapply coin_elem_of. destruct hX' as (hX1 & hX2).
           eapply hX2. 2: exact hp.
           apply elem_of_union_l, elem_of_singleton_2; reflexivity.
        -- eapply coin_elem_of. destruct hX' as (hX1 & hX2).
           eapply hX2. 2: exact hq.
           apply elem_of_union_r, elem_of_singleton_2; reflexivity.
    + intros hX.
      eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      constructor. intros t Ht.
      eapply choice_tau_inv in Ht as [-> | ->].
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_l, elem_of_singleton_2; reflexivity.
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_r, elem_of_singleton_2; reflexivity.
Qed.

(** Inversion helpers for τ-guarded binary choice under a forwarder. *)

Lemma choice_fw_tau_inv (p q : proc) (M : MO (ExtAct TypeOfActions)) t :
  ((g (𝛕 • p + 𝛕 • q)) ▷ M) ⟶ t -> t = (p ▷ M) \/ t = (q ▷ M).
Proof.
  intro Hstep. inversion Hstep; subst.
  - eapply choice_tau_inv in l as [-> | ->]; eauto.
  - inversion l.
  - exfalso. eapply choice_ext_inv; eauto.
Qed.

Lemma choice_fw_ext_inv (p q : proc) (M : MO (ExtAct TypeOfActions)) μ t :
  ((g (𝛕 • p + 𝛕 • q)) ▷ M) ⟶[μ] t ->
  exists M', t = ((g (𝛕 • p + 𝛕 • q)) ▷ M') /\ (forall r : proc, (r ▷ M) ⟶[μ] (r ▷ M')).
Proof.
  intro Hstep. inversion Hstep; subst.
  - exfalso. eapply choice_ext_inv; eauto.
  - eexists. split; eauto. intros r. eapply ParRight; eauto.
Qed.

Lemma choice_fw_wt_nil_inv (p q : proc) (M : MO (ExtAct TypeOfActions)) y :
  ((g (𝛕 • p + 𝛕 • q)) ▷ M) ⟹ y ->
  y = ((g (𝛕 • p + 𝛕 • q)) ▷ M) \/ (p ▷ M) ⟹ y \/ (q ▷ M) ⟹ y.
Proof.
  intro Hw. inversion Hw; subst.
  - eauto.
  - eapply choice_fw_tau_inv in l as [-> | ->]; eauto.
Qed.

Lemma choice_fw_wt_act_inv (p q : proc) (M : MO (ExtAct TypeOfActions)) μ y :
  ((g (𝛕 • p + 𝛕 • q)) ▷ M) ⟹{μ} y ->
  (exists M', y = ((g (𝛕 • p + 𝛕 • q)) ▷ M')
      /\ (p ▷ M) ⟹{μ} (p ▷ M') /\ (q ▷ M) ⟹{μ} (q ▷ M'))
  \/ (p ▷ M) ⟹{μ} y \/ (q ▷ M) ⟹{μ} y.
Proof.
  intro Hw. inversion Hw; subst.
  - eapply choice_fw_tau_inv in l as [-> | ->]; eauto.
  - eapply choice_fw_ext_inv in l as (M1 & -> & hstep).
    eapply choice_fw_wt_nil_inv in w as [-> | [hp | hq]].
    + left. exists M1. repeat split.
      * eapply lts_to_wt; eauto.
      * eapply lts_to_wt; eauto.
    + right. left. eapply wt_act; eauto.
    + right. right. eapply wt_act; eauto.
Qed.

Lemma choice_copre_rev (p q : proc) :
  forall (PRE : Chain (copre_m (P := proc * MO (ExtAct TypeOfActions))
                               (Q := proc * MO (ExtAct TypeOfActions))
                               (T := proc)))
    (M : MO (ExtAct TypeOfActions)),
    elem PRE ({[ p ▷ M; q ▷ M ]}) {[ (g (𝛕 • p + 𝛕 • q)) ▷ M ]}.
Proof.
  apply (tower (P := fun R => forall M,
    R ({[ p ▷ M; q ▷ M ]} : gset (proc * MO (ExtAct TypeOfActions)))
      {[ (g (𝛕 • p + 𝛕 • q)) ▷ M ]})).
  - intros S HS M R HR. eapply HS; eauto.
  - intros PRE CIH M.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply choice_fw_wt_nil_inv in hw as [-> | [hp | hq]].
        -- eapply CIH.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_l, elem_of_singleton_2; reflexivity.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_r, elem_of_singleton_2; reflexivity.
    + intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      eapply (lts_refuses_spec2 ((g (𝛕 • p + 𝛕 • q)) ▷ M) τ);
        [eexists (p ▷ M); eapply ParLeft, lts_choiceL; constructor | exact hst].
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        destruct hX' as (hX1 & hX2).
        eapply choice_fw_wt_act_inv in hw as [(M' & -> & hp & hq) | [hp | hq]].
        -- rewrite (union_difference_L {[p ▷ M'; q ▷ M']} X').
           ++ eapply coin_union_l, CIH.
           ++ intros z hz. apply elem_of_union in hz as [hz | hz];
                apply elem_of_singleton_1 in hz; subst z.
              ** eapply hX2. 2: exact hp.
                 apply elem_of_union_l, elem_of_singleton_2; reflexivity.
              ** eapply hX2. 2: exact hq.
                 apply elem_of_union_r, elem_of_singleton_2; reflexivity.
        -- eapply coin_elem_of.
           eapply hX2. 2: exact hp.
           apply elem_of_union_l, elem_of_singleton_2; reflexivity.
        -- eapply coin_elem_of.
           eapply hX2. 2: exact hq.
           apply elem_of_union_r, elem_of_singleton_2; reflexivity.
    + intros hX.
      eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      constructor. intros t Ht.
      eapply choice_fw_tau_inv in Ht as [-> | ->].
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_l, elem_of_singleton_2; reflexivity.
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_r, elem_of_singleton_2; reflexivity.
Qed.

Section Omega.

Definition omega : proc := pr_rec 0 (pr_var 0). (* rec X. X *)

Lemma omega_lts_omega : omega ⟶ omega.
Proof.
  replace (omega ⟶ omega) with (omega ⟶ (pr_subst 0 (pr_var 0) (pr_rec 0 (pr_var 0)))).
  - eapply lts_recursion.
  - simpl. reflexivity.
Qed.

Lemma omega_diverges : ¬ terminate omega.
Proof.
intro Ht. dependent induction Ht.
eapply H0.
- eapply omega_lts_omega.
- reflexivity.
Qed.

Lemma omega_is_bottom :
  forall (PRE : Chain (copre_m (P := proc) (Q := proc) (T := proc))) Y,
    elem PRE {[omega]} Y.
Proof.
apply (tower (P := fun R => forall Y, R ({[omega]} : gset proc) Y)).
- intros S HS Y R HR. eapply HS; eauto.
- intros PRE hco Y.
  constructor.
  + intros Y' hY'. apply hco.
  + intros hX y mem hst. exfalso.
    eapply omega_diverges.
    eapply termination_if_termination_set_helper; eauto.
    apply elem_of_singleton_2; reflexivity.
  + intros μ Y' X' hcnv hY' hX'. exfalso.
    eapply omega_diverges. eapply cnv_terminate.
    eapply convergence_forall_if_convergence_set; eauto.
    apply elem_of_singleton_2; reflexivity.
  + intros hX. exfalso.
    eapply omega_diverges.
    eapply termination_if_termination_set_helper; eauto.
    apply elem_of_singleton_2; reflexivity.
Qed.

End Omega.

(* In ACCS, recursion unfolding steps are "invertible" τ steps *)
Lemma rec_inv (n : nat) (p : proc) : forall α p',
  (pr_rec n p) ⟶{α} p' <-> (p' = pr_subst n p (pr_rec n p) /\ α = τ).
Proof.
intros α p'. split; intro Hs.
- inversion Hs; subst. eauto.
- destruct Hs; subst. eapply lts_recursion.
Qed.

(* Remark : proofs using the definition of must are not always difficult *)
Lemma musts_choice (p q : gproc) (t : proc) :
  must (g p) t -> must (g q) t -> must (g (p + q)) t.
Proof.
intros Hp Hq.
dependent induction Hp; [now constructor|].
destruct Hq; [now constructor|].
apply m_step.
- trivial.
- destruct ex as [[t1 t1'] H1']. inversion H1'; subst.
  + eexists. apply ParLeft. constructor. eassumption.
  + eexists. apply ParRight. eassumption.
  + eexists. eapply ParSync; eauto. constructor. eassumption.
- intros p' Hp'. inversion Hp'; subst.
  + apply pt. assumption.
  + apply pt0. assumption.
- intros e' He'. eapply H0; trivial. now apply et0.
- intros p' e' μ1 μ2 Hd Hμ1 Hμ2. inversion Hμ1; subst.
  + eapply com; eassumption.
  + eapply com0; eassumption.
Qed.

Section Example_2_1.
(** A nontrivial example with recursion *)

Definition unreliableW : proc :=
  pr_rec 0 (𝛕 • (cst "end" ! cst tt • 𝟘)
            + (cst "data" ? (𝛕 • ((cst "work" ! cst tt • 𝟘) ‖ pr_var 0)
                             + 𝛕 • (cst "bye" ! cst tt • 𝟘)))).

Definition reliableW : proc :=
  pr_rec 0 (𝛕 • (cst "end" ! cst tt • 𝟘)
            + (cst "data" ? ((cst "work" ! cst tt • 𝟘) ‖ pr_var 0))).

Lemma cgr_par_nil_l (p : proc) : (g 𝟘 ‖ p) ≡* p.
Proof.
  etransitivity.
  - eapply cgr_par_com.
  - eapply cgr_par_nil.
Qed.

Local Instance Proper_par n : Proper ((cgr n) ==> (cgr n) ==> (cgr n)) pr_par.
Proof.
  intros p p' Hp q q' Hq. eapply cgr_fullpar; eauto.
Qed.

(** Named sub-terms and one-step facts for the two workers. *)

Definition W_end : proc := cst "end" ! cst tt • 𝟘.
Definition W_work : proc := cst "work" ! cst tt • 𝟘.
Definition W_bye : proc := cst "bye" ! cst tt • 𝟘.
Definition Rbody : proc := g (𝛕 • W_end + (cst "data" ? (W_work ‖ reliableW))).
Definition UChoice : proc := g (𝛕 • (W_work ‖ unreliableW) + 𝛕 • W_bye).
Definition Ubody : proc := g (𝛕 • W_end + (cst "data" ? UChoice)).

Definition ch (s : String.string) : ChannelData := cst s.
Definition u1 : ValueData := cst tt.

Lemma reliableW_unfold : reliableW ⟶ Rbody.
Proof. exact (lts_recursion (x:=0)). Qed.

Lemma unreliableW_unfold : unreliableW ⟶ Ubody.
Proof. exact (lts_recursion (x:=0)). Qed.

Lemma rbody_end : Rbody ⟶ W_end.
Proof. eapply lts_choiceL. eapply lts_tau. Qed.

Lemma ubody_end : Ubody ⟶ W_end.
Proof. eapply lts_choiceL. eapply lts_tau. Qed.

Lemma rbody_input (v : ValueData) : Rbody ⟶[ActIn (ch "data", v)] (W_work ‖ reliableW).
Proof. eapply lts_choiceR. exact (lts_input (c := ch "data") (v := v)). Qed.

Lemma ubody_input (v : ValueData) : Ubody ⟶[ActIn (ch "data", v)] UChoice.
Proof. eapply lts_choiceR. exact (lts_input (c := ch "data") (v := v)). Qed.

Lemma uchoice_work : UChoice ⟶ (W_work ‖ unreliableW).
Proof. eapply lts_choiceL. eapply lts_tau. Qed.

Lemma uchoice_bye : UChoice ⟶ W_bye.
Proof. eapply lts_choiceR. eapply lts_tau. Qed.

Lemma wout_step (c : String.string) : (ch c ! u1 • 𝟘) ⟶[ActOut (ch c, u1)] (g 𝟘).
Proof. exact lts_output. Qed.

(** A decidable measure: number of buffered "data" outputs in a mailbox. *)

Definition is_data (a : ExtAct TypeOfActions) : Prop :=
  exists v, a = ActOut (ch "data", v).

Local Instance is_data_dec (a : ExtAct TypeOfActions) : Decision (is_data a).
Proof.
  destruct a as [(c, v) | (c, v)].
  - right. intros (v' & hv). inversion hv.
  - destruct (decide (c = ch "data")); subst.
    + left. exists v. reflexivity.
    + right. intros (v' & hv). inversion hv. eauto.
Defined.

Definition data_count (M : MO (ExtAct TypeOfActions)) : nat :=
  base.size (filter is_data M).

Lemma data_count_data (v : ValueData) m :
  data_count ({[+ ActOut (ch "data", v) +]} ⊎ m) = S (data_count m).
Proof.
  unfold data_count, MO in *.
  rewrite gmultiset_filter_disj_union.
  rewrite gmultiset_filter_singleton_True.
  - rewrite gmultiset_size_disj_union, gmultiset_size_singleton. reflexivity.
  - exists v. reflexivity.
Qed.

Lemma data_count_other a m :
  ¬ is_data a ->
  data_count ({[+ a +]} ⊎ m) = data_count m.
Proof.
  intro hn. unfold data_count, MO in *.
  rewrite gmultiset_filter_disj_union.
  rewrite gmultiset_filter_singleton_False; eauto.
  rewrite gmultiset_size_disj_union, gmultiset_size_empty. reflexivity.
Qed.

(* Adds k copies of the "work" output in parallel *)
Fixpoint addw (k : nat) (p : proc) : proc :=
  match k with 0 => p | S k' => W_work ‖ addw k' p end.

Lemma wwork_tau_inv t : W_work ⟶ t -> False.
Proof. intro h. inversion h. Qed.

Lemma wwork_input_inv c v t : W_work ⟶[ActIn (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

Lemma wwork_out_inv c v t : W_work ⟶[ActOut (c, v)] t ->
  c = ch "work" /\ v = u1 /\ t = g 𝟘.
Proof. intro h. inversion h; subst. eauto. Qed.

Lemma addw_input_inv k p c v t :
  addw k p ⟶[ActIn (c, v)] t ->
  exists p', p ⟶[ActIn (c, v)] p' /\ t = addw k p'.
Proof.
  revert t. induction k as [|k IH]; intros t h; simpl in *.
  - eauto.
  - inversion h; subst.
    + exfalso. eapply wwork_input_inv; eauto.
    + eapply IH in H3 as (p' & hp & ->). eauto.
Qed.

Lemma addw_tau_inv k p t :
  (forall v t', ¬ (p ⟶[ActIn (ch "work", v)] t')) ->
  addw k p ⟶ t ->
  exists p', p ⟶ p' /\ t = addw k p'.
Proof.
  intros hnw. revert t. induction k as [|k IH]; intros t h; simpl in *.
  - eauto.
  - inversion h; subst.
    + eapply wwork_out_inv in H1 as (-> & -> & ->).
      eapply addw_input_inv in H2 as (p' & hp & ->).
      exfalso. eapply hnw; eauto.
    + exfalso. eapply wwork_input_inv; eauto.
    + exfalso. eapply wwork_tau_inv; eauto.
    + eapply IH in H3 as (p' & hp & ->). eauto.
Qed.

(** One-step inversion facts for the workers' sub-terms. *)

Lemma reliableW_tau_inv t : reliableW ⟶ t -> t = Rbody.
Proof. intro h. inversion h; subst. reflexivity. Qed.

Lemma reliableW_input_inv c v t : reliableW ⟶[ActIn (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

Lemma reliableW_out_inv c v t : reliableW ⟶[ActOut (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

Lemma rbody_tau_inv t : Rbody ⟶ t -> t = W_end.
Proof.
  intro h. inversion h; subst.
  - inversion H3; subst. reflexivity.
  - inversion H3.
Qed.

Lemma rbody_input_inv c v t : Rbody ⟶[ActIn (c, v)] t ->
  c = ch "data" /\ t = W_work ‖ reliableW.
Proof.
  intro h. inversion h; subst.
  - inversion H3.
  - inversion H3; subst. eauto.
Qed.

Lemma rbody_out_inv c v t : Rbody ⟶[ActOut (c, v)] t -> False.
Proof.
  intro h. inversion h; subst.
  - inversion H3.
  - inversion H3.
Qed.

Lemma wend_tau_inv t : W_end ⟶ t -> False.
Proof. intro h. inversion h. Qed.

Lemma wend_input_inv c v t : W_end ⟶[ActIn (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

(** τ-step inversion for forwarder states. *)
Lemma fw_tau_inv (p : proc) (M : MO (ExtAct TypeOfActions)) s :
  ((p ▷ M) ⟶ s) ->
  (exists p', p ⟶ p' /\ s = (p' ▷ M))
  \/ (exists c v p' m, p ⟶[ActIn (c, v)] p'
        /\ M = {[+ ActOut (c, v) +]} ⊎ m /\ s = (p' ▷ m)).
Proof.
  intro h. inversion h; subst.
  - left. eauto.
  - inversion l.
  - destruct eq as (duo & nb).
    destruct nb as (a & haq). subst μ2.
    symmetry in duo. eapply simplify_match_output in duo. subst μ1.
    inversion l2; subst.
    + eapply simplify_match_output in duo. subst η.
      destruct nb as (a' & ha'). inversion ha'.
    + destruct a as (c, v).
      right. exists c, v, a2, b2. eauto.
Qed.

Lemma addw_par k p : addw k (W_work ‖ p) = addw (S k) p.
Proof.
  induction k as [|k IH]; simpl in *; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma rbody_no_work_input : forall v t', ¬ (Rbody ⟶[ActIn (ch "work", v)] t').
Proof.
  intros v t' h. eapply rbody_input_inv in h as (heq & _). inversion heq.
Qed.

Lemma reliableW_no_work_input : forall v t', ¬ (reliableW ⟶[ActIn (ch "work", v)] t').
Proof.
  intros v t' h. eapply reliableW_input_inv; eauto.
Qed.

Lemma wend_no_work_input : forall v t', ¬ (W_end ⟶[ActIn (ch "work", v)] t').
Proof.
  intros v t' h. eapply wend_input_inv; eauto.
Qed.

Lemma addw_end_fw_terminate k (M : MO (ExtAct TypeOfActions)) : (addw k W_end ▷ M) ⤓.
Proof.
  constructor. intros s hs.
  eapply fw_tau_inv in hs as [ (p' & hp & ->) | (c & v & p' & m & hp & -> & ->) ].
  - eapply addw_tau_inv in hp as (p'' & hp'' & ->);
      [ exfalso; eapply wend_tau_inv; eauto | eapply wend_no_work_input ].
  - eapply addw_input_inv in hp as (p'' & hp'' & ->).
    exfalso. eapply wend_input_inv; eauto.
Qed.

(** Termination of the reliable worker under any mailbox, in any parallel
    context of buffered "work" outputs. By strong induction on the number
    of buffered "data" messages. *)
Lemma addw_workers_fw_terminate : forall n (M : MO (ExtAct TypeOfActions)) k,
  data_count M = n ->
  (addw k reliableW ▷ M) ⤓ /\ (addw k Rbody ▷ M) ⤓.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros M k hM.
  assert ((addw k Rbody ▷ M) ⤓) as hRB.
  { constructor. intros s hs.
    eapply fw_tau_inv in hs as [ (p' & hp & ->) | (c & v & p' & m & hp & -> & ->) ].
    - eapply addw_tau_inv in hp as (p'' & hp'' & ->); [ | eapply rbody_no_work_input ].
      eapply rbody_tau_inv in hp''. subst p''.
      eapply addw_end_fw_terminate.
    - eapply addw_input_inv in hp as (p'' & hp'' & ->).
      eapply rbody_input_inv in hp'' as (-> & ->).
      rewrite addw_par.
      rewrite data_count_data in hM.
      destruct (IHn (data_count m) ltac:(lia) m (S k) eq_refl) as (hrel & _).
      exact hrel.
  }
  split; [ | exact hRB ].
  constructor. intros s hs.
  eapply fw_tau_inv in hs as [ (p' & hp & ->) | (c & v & p' & m & hp & -> & ->) ].
  - eapply addw_tau_inv in hp as (p'' & hp'' & ->); [ | eapply reliableW_no_work_input ].
    eapply reliableW_tau_inv in hp''. subst p''.
    exact hRB.
  - eapply addw_input_inv in hp as (p'' & hp'' & ->).
    exfalso. eapply reliableW_input_inv; eauto.
Qed.

Lemma reliableW_terminate (M : MO (ExtAct TypeOfActions)) : (reliableW ▷ M) ⤓.
Proof.
  destruct (addw_workers_fw_terminate (data_count M) M 0 eq_refl) as (h & _).
  exact h.
Qed.

Lemma addw_reliableW_terminate (M : MO (ExtAct TypeOfActions)) k : (addw k reliableW ▷ M) ⤓.
Proof.
  destruct (addw_workers_fw_terminate (data_count M) M k eq_refl) as (h & _).
  exact h.
Qed.

Lemma addw_rbody_terminate (M : MO (ExtAct TypeOfActions)) k : (addw k Rbody ▷ M) ⤓.
Proof.
  destruct (addw_workers_fw_terminate (data_count M) M k eq_refl) as (_ & h).
  exact h.
Qed.

(** Advance data messages: a multiset of n buffered "data" outputs with
    arbitrary payloads. *)
Inductive datas : nat -> MO (ExtAct TypeOfActions) -> Prop :=
| datas0 : datas 0 ∅
| datasS v n D : datas n D -> datas (S n) ({[+ ActOut (ch "data", v) +]} ⊎ D).

Fixpoint add_data (n : nat) (m : MO (ExtAct TypeOfActions)) : MO (ExtAct TypeOfActions) :=
  match n with
  | 0 => m
  | S n' => {[+ ActOut (ch "data", u1) +]} ⊎ add_data n' m
  end.

Lemma add_data_datas n m : exists D, datas n D /\ add_data n m = D ⊎ m.
Proof.
  induction n as [|n (D & hD & heq)]; simpl.
  - exists ∅. split; [constructor | multiset_solver].
  - exists ({[+ ActOut (ch "data", u1) +]} ⊎ D). split.
    + constructor. exact hD.
    + rewrite heq. multiset_solver.
Qed.

(** Parallel contexts made of live "work" outputs (true) and spent
    outputs (false). *)
Fixpoint wctx (ws : list bool) (p : proc) : proc :=
  match ws with
  | [] => p
  | b :: l => (if b then W_work else g 𝟘) ‖ wctx l p
  end.

Lemma wctx_app ws1 ws2 p : wctx (ws1 ++ ws2) p = wctx ws1 (wctx ws2 p).
Proof. induction ws1 as [|b l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma wctx_true_end ws p : wctx (ws ++ [true]) p = wctx ws (W_work ‖ p).
Proof. rewrite wctx_app. reflexivity. Qed.

Lemma gnil_tau_inv (t : proc) : (g 𝟘) ⟶ t -> False.
Proof. intro h. inversion h. Qed.

Lemma gnil_input_inv c v (t : proc) : (g 𝟘) ⟶[ActIn (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

Lemma gnil_out_inv c v (t : proc) : (g 𝟘) ⟶[ActOut (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

(** Lifting steps of the core through a context. *)
Lemma wctx_lift_tau ws p p' : p ⟶ p' -> wctx ws p ⟶ wctx ws p'.
Proof.
  intro h. induction ws as [|b l IH]; simpl; [exact h | eapply lts_parR; eauto].
Qed.

Lemma wctx_lift_input ws p p' c v :
  p ⟶[ActIn (c, v)] p' -> wctx ws p ⟶[ActIn (c, v)] wctx ws p'.
Proof.
  intro h. induction ws as [|b l IH]; simpl; [exact h | eapply lts_parR; eauto].
Qed.

Lemma wctx_lift_out ws p p' c v :
  p ⟶[ActOut (c, v)] p' -> wctx ws p ⟶[ActOut (c, v)] wctx ws p'.
Proof.
  intro h. induction ws as [|b l IH]; simpl; [exact h | eapply lts_parR; eauto].
Qed.

(** Firing the j-th live work of the context. *)
Fixpoint set_false (j : nat) (ws : list bool) : list bool :=
  match j, ws with
  | _, [] => []
  | 0, _ :: l => false :: l
  | S j', b :: l => b :: set_false j' l
  end.

Lemma wctx_fire ws j p :
  ws !! j = Some true ->
  wctx ws p ⟶[ActOut (ch "work", u1)] wctx (set_false j ws) p.
Proof.
  revert j. induction ws as [|b l IH]; intros j hj; [inversion hj|].
  destruct j as [|j]; simpl in *.
  - inversion hj; subst. eapply lts_parL. eapply lts_output.
  - eapply lts_parR. eapply IH. exact hj.
Qed.

(** Inversion of context steps. The core is assumed not to listen on
    "work" (true of every state of both workers). *)
Lemma wctx_input_inv ws p c v t :
  wctx ws p ⟶[ActIn (c, v)] t ->
  exists p', p ⟶[ActIn (c, v)] p' /\ t = wctx ws p'.
Proof.
  revert t. induction ws as [|b l IH]; intros t h; simpl in *.
  - eauto.
  - inversion h; subst.
    + exfalso. destruct b; [eapply wwork_input_inv | eapply gnil_input_inv]; eauto.
    + eapply IH in H3 as (p' & hp & ->). eauto.
Qed.

Lemma wctx_tau_inv ws p t :
  (forall v t', ¬ (p ⟶[ActIn (ch "work", v)] t')) ->
  wctx ws p ⟶ t ->
  exists p', p ⟶ p' /\ t = wctx ws p'.
Proof.
  intros hnw. revert t. induction ws as [|b l IH]; intros t h; simpl in *.
  - eauto.
  - inversion h; subst.
    + destruct b.
      * eapply wwork_out_inv in H1 as (-> & -> & ->).
        eapply wctx_input_inv in H2 as (p' & hp & ->).
        exfalso. eapply hnw; eauto.
      * exfalso. eapply gnil_out_inv; eauto.
    + exfalso. destruct b; [eapply wwork_input_inv | eapply gnil_input_inv]; eauto.
    + exfalso. destruct b; [eapply wwork_tau_inv | eapply gnil_tau_inv]; eauto.
    + eapply IH in H3 as (p' & hp & ->). eauto.
Qed.

Lemma wctx_out_inv ws p c v t :
  wctx ws p ⟶[ActOut (c, v)] t ->
  (exists j, ws !! j = Some true /\ c = ch "work" /\ v = u1
     /\ t = wctx (set_false j ws) p)
  \/ (exists p', p ⟶[ActOut (c, v)] p' /\ t = wctx ws p').
Proof.
  revert t. induction ws as [|b l IH]; intros t h; simpl in *.
  - right. eauto.
  - inversion h; subst.
    + destruct b.
      * eapply wwork_out_inv in H3 as (-> & -> & ->).
        left. exists 0. eauto.
      * exfalso. eapply gnil_out_inv; eauto.
    + eapply IH in H3 as [ (j & hj & -> & -> & ->) | (p' & hp & ->) ].
      * left. exists (S j). simpl. eauto.
      * right. eauto.
Qed.

Lemma wend_out_inv c v t : W_end ⟶[ActOut (c, v)] t ->
  c = ch "end" /\ v = u1 /\ t = g 𝟘.
Proof. intro h. inversion h; subst. eauto. Qed.

(** The four cores the reliable side ranges over. *)
Inductive rcore : Type := Crel | Cbody | Cend | Cnil.

Definition cproc (c : rcore) : proc :=
  match c with
  | Crel => reliableW | Cbody => Rbody | Cend => W_end | Cnil => g 𝟘
  end.

Lemma cproc_no_work_input c : forall v t', ¬ (cproc c ⟶[ActIn (ch "work", v)] t').
Proof.
  destruct c; simpl; intros v t' h.
  - eapply reliableW_no_work_input; eauto.
  - eapply rbody_no_work_input; eauto.
  - eapply wend_no_work_input; eauto.
  - eapply gnil_input_inv; eauto.
Qed.

Lemma cproc_tau_inv c t : cproc c ⟶ t ->
  (c = Crel /\ t = cproc Cbody) \/ (c = Cbody /\ t = cproc Cend).
Proof.
  destruct c; simpl; intro h.
  - eapply reliableW_tau_inv in h. subst. eauto.
  - eapply rbody_tau_inv in h. subst. eauto.
  - exfalso. eapply wend_tau_inv; eauto.
  - exfalso. eapply gnil_tau_inv; eauto.
Qed.

Lemma cproc_input_inv c cc v t : cproc c ⟶[ActIn (cc, v)] t ->
  c = Cbody /\ cc = ch "data" /\ t = W_work ‖ cproc Crel.
Proof.
  destruct c; simpl; intro h.
  - exfalso. eapply reliableW_input_inv; eauto.
  - eapply rbody_input_inv in h as (-> & ->). eauto.
  - exfalso. eapply wend_input_inv; eauto.
  - exfalso. eapply gnil_input_inv; eauto.
Qed.

Lemma cproc_out_inv c cc v t : cproc c ⟶[ActOut (cc, v)] t ->
  c = Cend /\ cc = ch "end" /\ v = u1 /\ t = cproc Cnil.
Proof.
  destruct c; simpl; intro h.
  - exfalso. eapply reliableW_out_inv; eauto.
  - exfalso. eapply rbody_out_inv; eauto.
  - eapply wend_out_inv in h as (-> & -> & ->). eauto.
  - exfalso. eapply gnil_out_inv; eauto.
Qed.

(** τ-step inversion for reliable-side states. *)
Lemma right_tau_inv ws c M s :
  (wctx ws (cproc c) ▷ M) ⟶ s ->
  (c = Crel /\ s = (wctx ws (cproc Cbody) ▷ M))
  \/ (c = Cbody /\ s = (wctx ws (cproc Cend) ▷ M))
  \/ (exists v m, c = Cbody /\ M = {[+ ActOut (ch "data", v) +]} ⊎ m
        /\ s = (wctx (ws ++ [true]) (cproc Crel) ▷ m)).
Proof.
  intro h.
  eapply fw_tau_inv in h as [ (p' & hp & ->) | (cc & v & p' & m & hp & -> & ->) ].
  - eapply wctx_tau_inv in hp as (p'' & hp'' & ->); [ | eapply cproc_no_work_input ].
    eapply cproc_tau_inv in hp'' as [ (-> & ->) | (-> & ->) ]; eauto.
  - eapply wctx_input_inv in hp as (p'' & hp'' & ->).
    eapply cproc_input_inv in hp'' as (-> & -> & ->).
    right. right. exists v, m. repeat split.
    rewrite wctx_true_end. reflexivity.
Qed.

(** Weak-τ characterisation of the reliable side: it can only convert
    buffered "data" into live "work"s and move along rel → body → end. *)
Lemma right_wt_nil_inv : forall y (ws : list bool) c (M : MO (ExtAct TypeOfActions)),
  (wctx ws (cproc c) ▷ M) ⟹ y ->
  c = Crel \/ c = Cbody \/ c = Cend ->
  exists n D m c', y = (wctx ((ws ++ repeat true n)%list) (cproc c') ▷ m)
    /\ M = D ⊎ m /\ datas n D
    /\ (c' = Crel \/ c' = Cbody \/ c' = Cend).
Proof.
  intros y ws c M hw.
  remember (wctx ws (cproc c) ▷ M) as x eqn:hx.
  remember ([] : trace (ExtAct TypeOfActions)) as tr eqn:htr.
  revert ws c M hx.
  induction hw as [ x | s x q y hstep hw IH | μ s x q y hstep hw IH ];
    intros ws c M hx hc; subst; try discriminate.
  - exists 0, ∅, M, c. rewrite app_nil_r. repeat split; eauto.
    + multiset_solver.
    + constructor.
  - eapply right_tau_inv in hstep
      as [ (-> & ->) | [ (-> & ->) | (v & m & -> & -> & ->) ] ].
    + edestruct (IH eq_refl ws Cbody M) as (n & D & m & c' & -> & -> & hD & hc');
        [ reflexivity | eauto | ].
      exists n, D, m, c'. repeat split; eauto.
    + edestruct (IH eq_refl ws Cend M) as (n & D & m & c' & -> & -> & hD & hc');
        [ reflexivity | eauto | ].
      exists n, D, m, c'. repeat split; eauto.
    + edestruct (IH eq_refl ((ws ++ [true])%list) Crel m) as (n & D & m' & c' & -> & -> & hD & hc');
        [ reflexivity | eauto | ].
      exists (S n), ({[+ ActOut (ch "data", v) +]} ⊎ D), m', c'.
      repeat split; eauto.
      * rewrite <- app_assoc. simpl. reflexivity.
      * multiset_solver.
      * constructor. exact hD.
Qed.

(** Constructive weak transitions of the unreliable side. *)

Lemma left_consume_one ws (v : ValueData) m :
  (wctx ws unreliableW ▷ ({[+ ActOut (ch "data", v) +]} ⊎ m))
    ⟹ (wctx ((ws ++ [true])%list) unreliableW ▷ m).
Proof.
  eapply wt_tau.
  { eapply ParLeft. eapply wctx_lift_tau. eapply unreliableW_unfold. }
  eapply wt_tau.
  { eapply (ParSync (ActIn (ch "data", v)) (ActOut (ch "data", v))).
    - split; [simpl; eauto | eexists; eauto].
    - eapply wctx_lift_input. eapply ubody_input.
    - eapply lts_multiset_minus. eexists; eauto. }
  eapply wt_tau.
  { eapply ParLeft. eapply wctx_lift_tau. eapply uchoice_work. }
  rewrite wctx_true_end. eapply wt_nil.
Qed.

Lemma left_consume_all : forall n D ws m,
  datas n D ->
  (wctx ws unreliableW ▷ (D ⊎ m))
    ⟹ (wctx ((ws ++ repeat true n)%list) unreliableW ▷ m).
Proof.
  intros n D ws m hD. revert ws m. induction hD as [| v n D hD IH]; intros ws m.
  - replace (∅ ⊎ m) with m by multiset_solver.
    rewrite app_nil_r. eapply wt_nil.
  - replace (({[+ ActOut (ch "data", v) +]} ⊎ D) ⊎ m)
      with ({[+ ActOut (ch "data", v) +]} ⊎ (D ⊎ m)) by multiset_solver.
    eapply wt_push_nil_left.
    + eapply left_consume_one.
    + replace ((ws ++ repeat true (S n))%list)
        with (((ws ++ [true]) ++ repeat true n)%list)
        by (rewrite <- app_assoc; reflexivity).
      eapply IH.
Qed.

Lemma left_to_end ws m :
  (wctx ws unreliableW ▷ m) ⟹ (wctx ws W_end ▷ m).
Proof.
  eapply wt_tau.
  { eapply ParLeft. eapply wctx_lift_tau. eapply unreliableW_unfold. }
  eapply wt_tau.
  { eapply ParLeft. eapply wctx_lift_tau. eapply ubody_end. }
  eapply wt_nil.
Qed.

Lemma left_consume_then_end n D ws m :
  datas n D ->
  (wctx ws unreliableW ▷ (D ⊎ m))
    ⟹ (wctx ((ws ++ repeat true n)%list) W_end ▷ m).
Proof.
  intro hD. eapply wt_push_nil_left.
  - eapply left_consume_all. exact hD.
  - eapply left_to_end.
Qed.

Lemma left_input_visible ws (v : ValueData) m :
  (wctx ws unreliableW ▷ m)
    ⟹{ActIn (ch "data", v)} (wctx ((ws ++ [true])%list) unreliableW ▷ m).
Proof.
  eapply wt_tau.
  { eapply ParLeft. eapply wctx_lift_tau. eapply unreliableW_unfold. }
  eapply wt_act.
  { eapply ParLeft. eapply wctx_lift_input. eapply ubody_input. }
  eapply wt_tau.
  { eapply ParLeft. eapply wctx_lift_tau. eapply uchoice_work. }
  rewrite wctx_true_end. eapply wt_nil.
Qed.

(** μ-step inversion for reliable-side states. *)
Lemma right_mu_inv ws c M μ s :
  (wctx ws (cproc c) ▷ M) ⟶[μ] s ->
  (exists j, ws !! j = Some true /\ μ = ActOut (ch "work", u1)
      /\ s = (wctx (set_false j ws) (cproc c) ▷ M))
  \/ (c = Cend /\ μ = ActOut (ch "end", u1) /\ s = (wctx ws (cproc Cnil) ▷ M))
  \/ (exists v, c = Cbody /\ μ = ActIn (ch "data", v)
      /\ s = (wctx ((ws ++ [true])%list) (cproc Crel) ▷ M))
  \/ (exists η, dual μ η /\ non_blocking η /\ s = (wctx ws (cproc c) ▷ ({[+ η +]} ⊎ M)))
  \/ (exists m, non_blocking μ /\ M = ({[+ μ +]} ⊎ m) /\ s = (wctx ws (cproc c) ▷ m)).
Proof.
  intro h. inversion h; subst.
  - destruct μ as [ (cc, v) | (cc, v) ].
    + eapply wctx_input_inv in l as (p' & hp & ->).
      eapply cproc_input_inv in hp as (-> & -> & ->).
      right. right. left. exists v. repeat split.
      rewrite wctx_true_end. reflexivity.
    + eapply wctx_out_inv in l as [ (j & hj & -> & -> & ->) | (p' & hp & ->) ].
      * left. eauto 8.
      * eapply cproc_out_inv in hp as (-> & -> & -> & ->).
        right. left. eauto.
  - inversion l; subst.
    + right. right. right. left. exists η. eauto.
    + right. right. right. right. exists b2. eauto.
Qed.

(** The reliable side terminates in any live/spent context. *)
Lemma wctx_end_fw_terminate ws (M : MO (ExtAct TypeOfActions)) c :
  c = Cend \/ c = Cnil ->
  (wctx ws (cproc c) ▷ M) ⤓.
Proof.
  intros hc.
  constructor. intros s hs.
  eapply fw_tau_inv in hs as [ (p' & hp & ->) | (cc & v & p' & m & hp & -> & ->) ].
  - eapply wctx_tau_inv in hp as (p'' & hp'' & ->); [ | eapply cproc_no_work_input ].
    eapply cproc_tau_inv in hp'' as [ (-> & _) | (-> & _) ]; destruct hc; discriminate.
  - eapply wctx_input_inv in hp as (p'' & hp'' & ->).
    eapply cproc_input_inv in hp'' as (-> & _ & _). destruct hc; discriminate.
Qed.

Lemma wctx_workers_fw_terminate : forall n (M : MO (ExtAct TypeOfActions)) ws,
  data_count M = n ->
  (wctx ws (cproc Crel) ▷ M) ⤓ /\ (wctx ws (cproc Cbody) ▷ M) ⤓.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros M ws hM.
  assert ((wctx ws (cproc Cbody) ▷ M) ⤓) as hRB.
  { constructor. intros s hs.
    eapply right_tau_inv in hs
      as [ (heq & ->) | [ (_ & ->) | (v & m & _ & -> & ->) ] ].
    - discriminate.
    - eapply wctx_end_fw_terminate. eauto.
    - rewrite data_count_data in hM.
      destruct (IHn (data_count m) ltac:(lia) m ((ws ++ [true])%list) eq_refl) as (hrel & _).
      exact hrel.
  }
  split; [ | exact hRB ].
  constructor. intros s hs.
  eapply right_tau_inv in hs
    as [ (_ & ->) | [ (heq & ->) | (v & m & heq & -> & ->) ] ].
  - exact hRB.
  - discriminate.
  - discriminate.
Qed.

Lemma datas_app a A b B : datas a A -> datas b B -> datas (a + b) (A ⊎ B).
Proof.
  intros hA. revert b B. induction hA as [| v n D hD IH]; intros b B hB; simpl.
  - replace (∅ ⊎ B) with B by multiset_solver. exact hB.
  - replace (({[+ ActOut (ch "data", v) +]} ⊎ D) ⊎ B)
      with ({[+ ActOut (ch "data", v) +]} ⊎ (D ⊎ B)) by multiset_solver.
    constructor. eapply IH. exact hB.
Qed.

Lemma right_nil_wt_nil_inv ws M y :
  (wctx ws (cproc Cnil) ▷ M) ⟹ y -> y = (wctx ws (cproc Cnil) ▷ M).
Proof.
  intro hw.
  remember (wctx ws (cproc Cnil) ▷ M) as x eqn:hx.
  remember ([] : trace (ExtAct TypeOfActions)) as tr eqn:htr.
  revert hx. induction hw; intros hx; subst; try discriminate.
  - reflexivity.
  - eapply right_tau_inv in l
      as [ (heq & _) | [ (heq & _) | (v & m & heq & _ & _) ] ]; discriminate.
Qed.

Lemma repeat_true_app (a b : nat) :
  (repeat true (a + b))%list = ((repeat true a) ++ (repeat true b))%list.
Proof. eapply repeat_app. Qed.

(** The coinductive generalisation: the unreliable worker with n buffered
    "data" messages in advance is below the reliable worker that has already
    converted this advance into n live "work" outputs. *)
Lemma unreliable_below_ctx :
  forall (PRE : Chain (copre_m (P := proc * MO (ExtAct TypeOfActions))
                        (Q := proc * MO (ExtAct TypeOfActions))
                        (T := proc)))
    (ws : list bool) n D (M : MO (ExtAct TypeOfActions)) c,
  datas n D -> (c = Crel \/ c = Cbody) ->
  elem PRE {[ wctx ws unreliableW ▷ (D ⊎ M) ]}
           {[ wctx ((ws ++ repeat true n)%list) (cproc c) ▷ M ]}.
Proof.
  apply (tower (P := fun R => forall ws n D M c,
    datas n D -> (c = Crel \/ c = Cbody) ->
    R ({[ wctx ws unreliableW ▷ (D ⊎ M) ]}
        : gset (proc * MO (ExtAct TypeOfActions)))
      {[ wctx ((ws ++ repeat true n)%list) (cproc c) ▷ M ]})).
  - intros S HS ws n D M c hD hc R HR. eapply HS; eauto.
  - intros PRE CIH ws n D M c hD hc.
    constructor.
    + (* weak τ descendants of the right *)
      intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply right_wt_nil_inv in hw
          as (n2 & D2 & m2 & c2 & -> & -> & hD2 & hc2);
          [ | destruct hc; subst; eauto ].
        destruct hc2 as [-> | [-> | ->]].
        -- replace (D ⊎ (D2 ⊎ m2)) with ((D ⊎ D2) ⊎ m2) by (unfold MO in *; multiset_solver).
           replace (((ws ++ repeat true n) ++ repeat true n2)%list)
             with ((ws ++ repeat true (n + n2))%list)
             by (rewrite repeat_true_app, app_assoc; reflexivity).
           eapply CIH; eauto using datas_app.
        -- replace (D ⊎ (D2 ⊎ m2)) with ((D ⊎ D2) ⊎ m2) by (unfold MO in *; multiset_solver).
           replace (((ws ++ repeat true n) ++ repeat true n2)%list)
             with ((ws ++ repeat true (n + n2))%list)
             by (rewrite repeat_true_app, app_assoc; reflexivity).
           eapply CIH; eauto using datas_app.
        -- eapply coin_wt_nil_singleton.
           replace (D ⊎ (D2 ⊎ m2)) with ((D ⊎ D2) ⊎ m2) by (unfold MO in *; multiset_solver).
           replace (((ws ++ repeat true n) ++ repeat true n2)%list)
             with ((ws ++ repeat true (n + n2))%list)
             by (rewrite repeat_true_app, app_assoc; reflexivity).
           eapply left_consume_then_end. eauto using datas_app.
    + (* the right is not stable *)
      intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      destruct hc; subst c.
      * eapply (lts_refuses_spec2
                  (wctx ((ws ++ repeat true n)%list) (cproc Crel) ▷ M) τ);
          [ eexists; eapply ParLeft, wctx_lift_tau, reliableW_unfold | exact hst ].
      * eapply (lts_refuses_spec2
                  (wctx ((ws ++ repeat true n)%list) (cproc Cbody) ▷ M) τ);
          [ eexists; eapply ParLeft, wctx_lift_tau, rbody_end | exact hst ].
    + (* weak μ descendants of the right *)
      intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        destruct hX' as (hX1 & hX2).
        eapply wt_decomp_one in hw as (r1 & r2 & hw1 & hstep & hw2).
        eapply right_wt_nil_inv in hw1
          as (n1 & D1 & m1 & c1 & -> & -> & hD1 & hc1);
          [ | destruct hc; subst; eauto ].
        set (ws1 := (((ws ++ repeat true n) ++ repeat true n1))%list) in *.
        assert (hL1 : (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ m1)))
                        ⟹ (wctx ws1 unreliableW ▷ m1)).
        { replace (D ⊎ (D1 ⊎ m1)) with ((D ⊎ D1) ⊎ m1) by (unfold MO in *; multiset_solver).
          replace ws1 with ((ws ++ repeat true (n + n1))%list)
            by (unfold ws1; rewrite repeat_true_app, app_assoc; reflexivity).
          eapply left_consume_all. eauto using datas_app. }
        eapply right_mu_inv in hstep
          as [ (j & hj & -> & ->)
             | [ (-> & -> & ->)
             | [ (v & -> & -> & ->)
             | [ (η & hduo & hnb & ->)
             | (m' & hnb & -> & ->) ] ] ] ].
        -- (* a live work fires *)
           eapply right_wt_nil_inv in hw2
             as (n2 & D2 & m2 & c2 & -> & -> & hD2 & hc2); eauto.
           assert (hL2 : (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ (D2 ⊎ m2))))
                    ⟹{ActOut (ch "work", u1)}
                    (wctx (set_false j ws1) unreliableW ▷ (D2 ⊎ m2))).
           { eapply wt_push_nil_left; [ exact hL1 | ].
             eapply wt_act; [ eapply ParLeft, wctx_fire; exact hj | eapply wt_nil ]. }
           destruct hc2 as [-> | [-> | ->]].
           ++ rewrite (union_difference_singleton_L
                 (wctx (set_false j ws1) unreliableW ▷ (D2 ⊎ m2)) X').
              ** eapply coin_union_l.
                 eapply (CIH (set_false j ws1) n2 D2 m2 Crel); eauto.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hL2 ].
           ++ rewrite (union_difference_singleton_L
                 (wctx (set_false j ws1) unreliableW ▷ (D2 ⊎ m2)) X').
              ** eapply coin_union_l.
                 eapply (CIH (set_false j ws1) n2 D2 m2 Cbody); eauto.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hL2 ].
           ++ eapply coin_elem_of.
              eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
              eapply wt_push_nil_left; [ exact hL1 | ].
              eapply wt_act; [ eapply ParLeft, wctx_fire; exact hj | ].
              replace (D1 ⊎ (D2 ⊎ m2)) with ((D1 ⊎ D2) ⊎ m2) in hL1 |- * by (unfold MO in *; multiset_solver).
              eapply wt_push_nil_left.
              ** eapply left_consume_all. exact hD2.
              ** eapply left_to_end.
        -- (* the "end" output fires *)
           eapply right_nil_wt_nil_inv in hw2. subst x.
           eapply coin_elem_of.
           eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
           eapply wt_push_nil_left; [ exact hL1 | ].
           eapply wt_push_nil_left; [ eapply left_to_end | ].
           eapply wt_act; [ | eapply wt_nil ].
           eapply ParLeft. eapply wctx_lift_out. exact lts_output.
        -- (* a visible "data" input of the process *)
           eapply right_wt_nil_inv in hw2
             as (n2 & D2 & m2 & c2 & -> & -> & hD2 & hc2); eauto.
           assert (hL2 : (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ (D2 ⊎ m2))))
                    ⟹{ActIn (ch "data", v)}
                    (wctx ((ws1 ++ [true])%list) unreliableW ▷ (D2 ⊎ m2))).
           { eapply wt_push_nil_left; [ exact hL1 | ].
             eapply left_input_visible. }
           destruct hc2 as [-> | [-> | ->]].
           ++ rewrite (union_difference_singleton_L
                 (wctx ((ws1 ++ [true])%list) unreliableW ▷ (D2 ⊎ m2)) X').
              ** eapply coin_union_l.
                 eapply (CIH ((ws1 ++ [true])%list) n2 D2 m2 Crel); eauto.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hL2 ].
           ++ rewrite (union_difference_singleton_L
                 (wctx ((ws1 ++ [true])%list) unreliableW ▷ (D2 ⊎ m2)) X').
              ** eapply coin_union_l.
                 eapply (CIH ((ws1 ++ [true])%list) n2 D2 m2 Cbody); eauto.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hL2 ].
           ++ eapply coin_elem_of.
              eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
              eapply wt_push_nil_left; [ exact hL1 | ].
              eapply wt_push_left; [ eapply left_input_visible | ].
              eapply left_consume_then_end. exact hD2.
        -- (* the mailbox buffers a new message *)
           eapply right_wt_nil_inv in hw2
             as (n2 & D2 & m2 & c2 & -> & heqm & hD2 & hc2); eauto.
           assert (hLa : (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ m1)))
                    ⟹{μ} (wctx ws unreliableW ▷ ({[+ η +]} ⊎ (D ⊎ (D1 ⊎ m1))))).
           { eapply wt_act; [ | eapply wt_nil ].
             eapply ParRight. eapply lts_multiset_add; eauto. }
           destruct hc2 as [-> | [-> | ->]].
           ++ rewrite (union_difference_singleton_L
                 (wctx ws unreliableW ▷ ({[+ η +]} ⊎ (D ⊎ (D1 ⊎ m1)))) X').
              ** eapply coin_union_l.
                 assert (heqm' : {[+ η +]} ⊎ m1 = D2 ⊎ m2) by (exact heqm).
                   replace ({[+ η +]} ⊎ (D ⊎ (D1 ⊎ m1)))
                     with ((D ⊎ (D1 ⊎ D2)) ⊎ m2)
                     by (unfold MO in *; multiset_solver).
                 replace ((ws1 ++ repeat true n2)%list)
                   with ((ws ++ repeat true (n + (n1 + n2)))%list)
                   by (unfold ws1; rewrite !repeat_true_app, !app_assoc; reflexivity).
                 eapply CIH; eauto using datas_app.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hLa ].
           ++ rewrite (union_difference_singleton_L
                 (wctx ws unreliableW ▷ ({[+ η +]} ⊎ (D ⊎ (D1 ⊎ m1)))) X').
              ** eapply coin_union_l.
                 assert (heqm' : {[+ η +]} ⊎ m1 = D2 ⊎ m2) by (exact heqm).
                   replace ({[+ η +]} ⊎ (D ⊎ (D1 ⊎ m1)))
                     with ((D ⊎ (D1 ⊎ D2)) ⊎ m2)
                     by (unfold MO in *; multiset_solver).
                 replace ((ws1 ++ repeat true n2)%list)
                   with ((ws ++ repeat true (n + (n1 + n2)))%list)
                   by (unfold ws1; rewrite !repeat_true_app, !app_assoc; reflexivity).
                 eapply CIH; eauto using datas_app.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hLa ].
           ++ eapply coin_elem_of.
              eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
              eapply wt_push_left; [ exact hLa | ].
              assert (heqm' : {[+ η +]} ⊎ m1 = D2 ⊎ m2) by (exact heqm).
                replace ({[+ η +]} ⊎ (D ⊎ (D1 ⊎ m1)))
                  with ((D ⊎ (D1 ⊎ D2)) ⊎ m2)
                  by (unfold MO in *; multiset_solver).
              replace ((ws1 ++ repeat true n2)%list)
                with ((ws ++ repeat true (n + (n1 + n2)))%list)
                by (unfold ws1; rewrite !repeat_true_app, !app_assoc; reflexivity).
              eapply left_consume_then_end. eauto using datas_app.
        -- (* the mailbox delivers a buffered message *)
           eapply right_wt_nil_inv in hw2
             as (n2 & D2 & m2 & c2 & -> & heqm & hD2 & hc2); eauto.
           assert (hLb : (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ ({[+ μ +]} ⊎ m'))))
                    ⟹{μ} (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ m')))).
           { eapply wt_act; [ | eapply wt_nil ].
             eapply ParRight.
             replace (D ⊎ (D1 ⊎ ({[+ μ +]} ⊎ m')))
               with ({[+ μ +]} ⊎ (D ⊎ (D1 ⊎ m'))) by (unfold MO in *; multiset_solver).
             eapply lts_multiset_minus; eauto. }
           destruct hc2 as [-> | [-> | ->]].
           ++ rewrite (union_difference_singleton_L
                 (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ m'))) X').
              ** eapply coin_union_l.
                 replace (D ⊎ (D1 ⊎ m'))
                   with ((D ⊎ (D1 ⊎ D2)) ⊎ m2)
                   by (unfold MO in *; multiset_solver).
                 replace ((ws1 ++ repeat true n2)%list)
                   with ((ws ++ repeat true (n + (n1 + n2)))%list)
                   by (unfold ws1; rewrite !repeat_true_app, !app_assoc; reflexivity).
                 eapply CIH; eauto using datas_app.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hLb ].
           ++ rewrite (union_difference_singleton_L
                 (wctx ws unreliableW ▷ (D ⊎ (D1 ⊎ m'))) X').
              ** eapply coin_union_l.
                 replace (D ⊎ (D1 ⊎ m'))
                   with ((D ⊎ (D1 ⊎ D2)) ⊎ m2)
                   by (unfold MO in *; multiset_solver).
                 replace ((ws1 ++ repeat true n2)%list)
                   with ((ws ++ repeat true (n + (n1 + n2)))%list)
                   by (unfold ws1; rewrite !repeat_true_app, !app_assoc; reflexivity).
                 eapply CIH; eauto using datas_app.
              ** eapply hX2; [ apply elem_of_singleton_2; reflexivity | exact hLb ].
           ++ eapply coin_elem_of.
              eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
              eapply wt_push_left; [ exact hLb | ].
              replace (D ⊎ (D1 ⊎ m'))
                with ((D ⊎ (D1 ⊎ D2)) ⊎ m2)
                by (unfold MO in *; multiset_solver).
              replace ((ws1 ++ repeat true n2)%list)
                with ((ws ++ repeat true (n + (n1 + n2)))%list)
                by (unfold ws1; rewrite !repeat_true_app, !app_assoc; reflexivity).
              eapply left_consume_then_end. eauto using datas_app.
    + (* the right terminates *)
      intros hX. eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      destruct (wctx_workers_fw_terminate
                  (data_count M) M ((ws ++ repeat true n)%list) eq_refl)
        as (hrel & hbody).
      destruct hc; subst c; eauto.
Qed.

Example unreliable_reliable : unreliableW ⊑ₘᵤₛₜᵢ reliableW.
Proof.
  eapply must_iff_tower_co_inductive_acceptance_VACCS.
  unfold copre. eapply gfp_prop. intros PRE.
  assert (h := unreliable_below_ctx PRE [] 0 ∅ ∅ Crel datas0 (or_introl eq_refl)).
  simpl in h.
  replace ((∅ : MO (ExtAct TypeOfActions)) ⊎ (∅ : MO (ExtAct TypeOfActions)))
    with ((∅ : MO (ExtAct TypeOfActions))) in h by (unfold MO in *; multiset_solver).
  exact h.
Qed.

End Example_2_1.

(** * Code hoisting: an output can be factored out of a τ-guarded choice. *)
Section Code_Hoisting.

Variable a : String.string.
Variable vv : ValueData.
Variables p q : proc.

Let Wo : proc := ch a ! vv • 𝟘.
Let C : proc := g (𝛕 • p + 𝛕 • q).
Let GL : proc := g (𝛕 • (Wo ‖ p) + 𝛕 • (Wo ‖ q)).

Lemma wo_tau_inv t : Wo ⟶ t -> False.
Proof. intro h. inversion h. Qed.

Lemma wo_in_inv c v t : Wo ⟶[ActIn (c, v)] t -> False.
Proof. intro h. inversion h. Qed.

Lemma wo_out_inv c v t : Wo ⟶[ActOut (c, v)] t ->
  c = ch a /\ v = vv /\ t = g 𝟘.
Proof. intro h. inversion h; subst. eauto. Qed.

Lemma WC_tau_inv t : (Wo ‖ C) ⟶ t -> t = (Wo ‖ p) \/ t = (Wo ‖ q).
Proof.
  intro h. inversion h; subst.
  - exfalso. eapply choice_ext_inv; eauto.
  - exfalso. eapply wo_in_inv; eauto.
  - exfalso. eapply wo_tau_inv; eauto.
  - eapply choice_tau_inv in H3 as [-> | ->]; eauto.
Qed.

Lemma NC_tau_inv t : (g 𝟘 ‖ C) ⟶ t -> t = (g 𝟘 ‖ p) \/ t = (g 𝟘 ‖ q).
Proof.
  intro h. inversion h; subst.
  - exfalso. eapply gnil_out_inv; eauto.
  - exfalso. eapply gnil_input_inv; eauto.
  - exfalso. eapply gnil_tau_inv; eauto.
  - eapply choice_tau_inv in H3 as [-> | ->]; eauto.
Qed.

Lemma WC_wt_nil_inv y :
  (Wo ‖ C) ⟹ y -> y = (Wo ‖ C) \/ (Wo ‖ p) ⟹ y \/ (Wo ‖ q) ⟹ y.
Proof.
  intro hw. inversion hw; subst.
  - eauto.
  - eapply WC_tau_inv in l as [-> | ->]; eauto.
Qed.

Lemma NC_wt_nil_inv y :
  (g 𝟘 ‖ C) ⟹ y -> y = (g 𝟘 ‖ C) \/ (g 𝟘 ‖ p) ⟹ y \/ (g 𝟘 ‖ q) ⟹ y.
Proof.
  intro hw. inversion hw; subst.
  - eauto.
  - eapply NC_tau_inv in l as [-> | ->]; eauto.
Qed.

Lemma WC_mu_inv μ t : (Wo ‖ C) ⟶[μ] t ->
  μ = ActOut (ch a, vv) /\ t = (g 𝟘 ‖ C).
Proof.
  intro h. inversion h; subst.
  - destruct μ as [(c, v) | (c, v)].
    + exfalso. eapply wo_in_inv; eauto.
    + eapply wo_out_inv in H3 as (-> & -> & ->). eauto.
  - exfalso. eapply choice_ext_inv; eauto.
Qed.

Lemma NC_mu_inv μ t : (g 𝟘 ‖ C) ⟶[μ] t -> False.
Proof.
  intro h. inversion h; subst.
  - destruct μ as [(c, v) | (c, v)];
      [ eapply gnil_input_inv | eapply gnil_out_inv ]; eauto.
  - eapply choice_ext_inv; eauto.
Qed.

Lemma gl_to_wp : GL ⟶ (Wo ‖ p).
Proof. eapply lts_choiceL. eapply lts_tau. Qed.

Lemma gl_to_wq : GL ⟶ (Wo ‖ q).
Proof. eapply lts_choiceR. eapply lts_tau. Qed.

Lemma wp_fire (r : proc) : (Wo ‖ r) ⟶[ActOut (ch a, vv)] (g 𝟘 ‖ r).
Proof. eapply lts_parL. exact lts_output. Qed.

(** τ-guarded choice under a spent output. *)
Lemma nchoice_copre_rev :
  forall (PRE : Chain (copre_m (P := proc) (Q := proc) (T := proc))),
    elem PRE ({[ g 𝟘 ‖ p; g 𝟘 ‖ q ]}) {[ g 𝟘 ‖ C ]}.
Proof.
  apply (tower (P := fun R =>
    R ({[ g 𝟘 ‖ p; g 𝟘 ‖ q ]} : gset proc) {[ g 𝟘 ‖ C ]})).
  - intros S HS R HR. eapply HS; eauto.
  - intros PRE CIH.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply NC_wt_nil_inv in hw as [-> | [hp | hq]].
        -- eapply CIH.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_l, elem_of_singleton_2; reflexivity.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_r, elem_of_singleton_2; reflexivity.
    + intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      eapply (lts_refuses_spec2 (g 𝟘 ‖ C) τ);
        [ eexists; eapply lts_parR, lts_choiceL; constructor | exact hst ].
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        destruct hX' as (hX1 & hX2).
        inversion hw; subst.
        -- eapply NC_tau_inv in l as [-> | ->].
           ++ eapply coin_elem_of. eapply hX2. 2: eauto.
              apply elem_of_union_l, elem_of_singleton_2; reflexivity.
           ++ eapply coin_elem_of. eapply hX2. 2: eauto.
              apply elem_of_union_r, elem_of_singleton_2; reflexivity.
        -- exfalso. eapply NC_mu_inv; eauto.
    + intros hX.
      eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      constructor. intros t Ht.
      eapply NC_tau_inv in Ht as [-> | ->].
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_l, elem_of_singleton_2; reflexivity.
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_r, elem_of_singleton_2; reflexivity.
Qed.

Example code_hoisting_output :
  ({[ GL ]} : gset proc) ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ Wo ‖ C ]} : gset proc).
Proof.
  unfold copre. eapply gfp_prop. intros PRE. revert PRE.
  apply (tower (P := fun R => R ({[ GL ]} : gset proc) {[ Wo ‖ C ]})).
  - intros S HS R HR. eapply HS; eauto.
  - intros PRE CIH.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply WC_wt_nil_inv in hw as [-> | [hp | hq]].
        -- eapply CIH.
        -- eapply coin_wt_nil_singleton.
           eapply wt_tau; [ eapply gl_to_wp | exact hp ].
        -- eapply coin_wt_nil_singleton.
           eapply wt_tau; [ eapply gl_to_wq | exact hq ].
    + intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      eapply (lts_refuses_spec2 (Wo ‖ C) τ);
        [ eexists; eapply lts_parR, lts_choiceL; constructor | exact hst ].
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        destruct hX' as (hX1 & hX2).
        inversion hw; subst.
        -- (* first a τ: the choice resolves, then the left mimics exactly *)
           eapply WC_tau_inv in l as [-> | ->].
           ++ eapply coin_elem_of. eapply hX2.
              { apply elem_of_singleton_2; reflexivity. }
              eapply wt_tau; [ eapply gl_to_wp | eauto ].
           ++ eapply coin_elem_of. eapply hX2.
              { apply elem_of_singleton_2; reflexivity. }
              eapply wt_tau; [ eapply gl_to_wq | eauto ].
        -- (* the output fires first *)
           eapply WC_mu_inv in l as (-> & ->).
           eapply NC_wt_nil_inv in w as [-> | [hp | hq]].
           ++ rewrite (union_difference_L {[g 𝟘 ‖ p; g 𝟘 ‖ q]} X').
              ** eapply coin_union_l. eapply nchoice_copre_rev.
              ** intros z hz. apply elem_of_union in hz as [hz | hz];
                   apply elem_of_singleton_1 in hz; subst z.
                 --- eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
                     eapply wt_tau; [ eapply gl_to_wp | ].
                     eapply wt_act; [ eapply wp_fire | eapply wt_nil ].
                 --- eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
                     eapply wt_tau; [ eapply gl_to_wq | ].
                     eapply wt_act; [ eapply wp_fire | eapply wt_nil ].
           ++ eapply coin_elem_of. eapply hX2.
              { apply elem_of_singleton_2; reflexivity. }
              eapply wt_tau; [ eapply gl_to_wp | ].
              eapply wt_act; [ eapply wp_fire | exact hp ].
           ++ eapply coin_elem_of. eapply hX2.
              { apply elem_of_singleton_2; reflexivity. }
              eapply wt_tau; [ eapply gl_to_wq | ].
              eapply wt_act; [ eapply wp_fire | exact hq ].
    + intros hX.
      eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      assert (GL ⤓) as hGL.
      { eapply termination_if_termination_set_helper; eauto.
        apply elem_of_singleton_2; reflexivity. }
      destruct hGL as [hGL].
      constructor. intros t Ht.
      eapply WC_tau_inv in Ht as [-> | ->]; eauto using gl_to_wp, gl_to_wq.
Qed.

End Code_Hoisting.

(** * Code hoisting under a forwarder. *)
Section Code_Hoisting_FW.

Variable a : String.string.
Variable vv : ValueData.
Variables p q : proc.

Let Wo : proc := ch a ! vv • 𝟘.
Let C : proc := g (𝛕 • p + 𝛕 • q).
Let GL : proc := g (𝛕 • (Wo ‖ p) + 𝛕 • (Wo ‖ q)).

Lemma WC_in_inv c v t : (Wo ‖ C) ⟶[ActIn (c, v)] t -> False.
Proof.
  intro h. inversion h; subst.
  - eapply wo_in_inv; eauto.
  - eapply choice_ext_inv; eauto.
Qed.

Lemma NC_in_inv c v t : (g 𝟘 ‖ C) ⟶[ActIn (c, v)] t -> False.
Proof.
  intro h. inversion h; subst.
  - eapply gnil_input_inv; eauto.
  - eapply choice_ext_inv; eauto.
Qed.

Lemma WCM_tau_inv (M : MO (ExtAct TypeOfActions)) s :
  ((Wo ‖ C) ▷ M) ⟶ s -> s = ((Wo ‖ p) ▷ M) \/ s = ((Wo ‖ q) ▷ M).
Proof.
  intro h.
  eapply fw_tau_inv in h as [ (p' & hp & ->) | (cc & v & p' & m & hp & -> & ->) ].
  - eapply WC_tau_inv in hp as [-> | ->]; eauto.
  - exfalso. eapply WC_in_inv; eauto.
Qed.

Lemma NCM_tau_inv (M : MO (ExtAct TypeOfActions)) s :
  ((g 𝟘 ‖ C) ▷ M) ⟶ s -> s = ((g 𝟘 ‖ p) ▷ M) \/ s = ((g 𝟘 ‖ q) ▷ M).
Proof.
  intro h.
  eapply fw_tau_inv in h as [ (p' & hp & ->) | (cc & v & p' & m & hp & -> & ->) ].
  - eapply NC_tau_inv in hp as [-> | ->]; eauto.
  - exfalso. eapply NC_in_inv; eauto.
Qed.

Lemma WCM_wt_nil_inv (M : MO (ExtAct TypeOfActions)) y :
  ((Wo ‖ C) ▷ M) ⟹ y ->
  y = ((Wo ‖ C) ▷ M) \/ ((Wo ‖ p) ▷ M) ⟹ y \/ ((Wo ‖ q) ▷ M) ⟹ y.
Proof.
  intro hw. inversion hw; subst.
  - eauto.
  - eapply WCM_tau_inv in l as [-> | ->]; eauto.
Qed.

Lemma NCM_wt_nil_inv (M : MO (ExtAct TypeOfActions)) y :
  ((g 𝟘 ‖ C) ▷ M) ⟹ y ->
  y = ((g 𝟘 ‖ C) ▷ M) \/ ((g 𝟘 ‖ p) ▷ M) ⟹ y \/ ((g 𝟘 ‖ q) ▷ M) ⟹ y.
Proof.
  intro hw. inversion hw; subst.
  - eauto.
  - eapply NCM_tau_inv in l as [-> | ->]; eauto.
Qed.

Lemma WCM_mu_inv (M : MO (ExtAct TypeOfActions)) μ s :
  ((Wo ‖ C) ▷ M) ⟶[μ] s ->
  (μ = ActOut (ch a, vv) /\ s = ((g 𝟘 ‖ C) ▷ M))
  \/ (exists η, dual μ η /\ non_blocking η /\ s = ((Wo ‖ C) ▷ ({[+ η +]} ⊎ M)))
  \/ (exists m, non_blocking μ /\ M = ({[+ μ +]} ⊎ m) /\ s = ((Wo ‖ C) ▷ m)).
Proof.
  intro h. inversion h; subst.
  - destruct μ as [ (cc, v) | (cc, v) ].
    + exfalso. eapply WC_in_inv; eauto.
    + eapply WC_mu_inv in l as (-> & ->). eauto.
  - inversion l; subst.
    + right. left. exists η. eauto.
    + right. right. exists b2. eauto.
Qed.

Lemma NCM_mu_inv (M : MO (ExtAct TypeOfActions)) μ s :
  ((g 𝟘 ‖ C) ▷ M) ⟶[μ] s ->
  (exists η, dual μ η /\ non_blocking η /\ s = ((g 𝟘 ‖ C) ▷ ({[+ η +]} ⊎ M)))
  \/ (exists m, non_blocking μ /\ M = ({[+ μ +]} ⊎ m) /\ s = ((g 𝟘 ‖ C) ▷ m)).
Proof.
  intro h. inversion h; subst.
  - exfalso. eapply NC_mu_inv; eauto.
  - inversion l; subst.
    + left. exists η. eauto.
    + right. exists b2. eauto.
Qed.

Lemma nchoice_copre_rev_fw :
  forall (PRE : Chain (copre_m (P := proc * MO (ExtAct TypeOfActions))
                       (Q := proc * MO (ExtAct TypeOfActions))
                       (T := proc)))
    (M : MO (ExtAct TypeOfActions)),
    elem PRE ({[ (g 𝟘 ‖ p) ▷ M; (g 𝟘 ‖ q) ▷ M ]}) {[ (g 𝟘 ‖ C) ▷ M ]}.
Proof.
  apply (tower (P := fun R => forall M,
    R ({[ (g 𝟘 ‖ p) ▷ M; (g 𝟘 ‖ q) ▷ M ]}
        : gset (proc * MO (ExtAct TypeOfActions)))
      {[ (g 𝟘 ‖ C) ▷ M ]})).
  - intros S HS M R HR. eapply HS; eauto.
  - intros PRE CIH M.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply NCM_wt_nil_inv in hw as [-> | [hp | hq]].
        -- eapply CIH.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_l, elem_of_singleton_2; reflexivity.
        -- eapply coin_choose.
           2: eapply coin_wt_nil_singleton; eauto.
           apply elem_of_union_r, elem_of_singleton_2; reflexivity.
    + intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      eapply (lts_refuses_spec2 ((g 𝟘 ‖ C) ▷ M) τ);
        [ eexists; eapply ParLeft, lts_parR, lts_choiceL; constructor | exact hst ].
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        destruct hX' as (hX1 & hX2).
        inversion hw; subst.
        -- eapply NCM_tau_inv in l as [-> | ->].
           ++ eapply coin_elem_of. eapply hX2. 2: eauto.
              apply elem_of_union_l, elem_of_singleton_2; reflexivity.
           ++ eapply coin_elem_of. eapply hX2. 2: eauto.
              apply elem_of_union_r, elem_of_singleton_2; reflexivity.
        -- eapply NCM_mu_inv in l
             as [ (η & hduo & hnb & ->) | (m & hnb & -> & ->) ].
           ++ eapply NCM_wt_nil_inv in w as [-> | [hp | hq]].
              ** rewrite (union_difference_L
                    {[(g 𝟘 ‖ p) ▷ ({[+ η +]} ⊎ M); (g 𝟘 ‖ q) ▷ ({[+ η +]} ⊎ M)]} X').
                 --- eapply coin_union_l. eapply CIH.
                 --- intros z hz. apply elem_of_union in hz as [hz | hz];
                       apply elem_of_singleton_1 in hz; subst z.
                     +++ eapply hX2; [ apply elem_of_union_l, elem_of_singleton_2; reflexivity | ].
                         eapply wt_act; [ | eapply wt_nil ].
                         eapply ParRight. eapply lts_multiset_add; eauto.
                     +++ eapply hX2; [ apply elem_of_union_r, elem_of_singleton_2; reflexivity | ].
                         eapply wt_act; [ | eapply wt_nil ].
                         eapply ParRight. eapply lts_multiset_add; eauto.
              ** eapply coin_elem_of.
                 eapply hX2; [ apply elem_of_union_l, elem_of_singleton_2; reflexivity | ].
                 eapply wt_act; [ | exact hp ].
                 eapply ParRight. eapply lts_multiset_add; eauto.
              ** eapply coin_elem_of.
                 eapply hX2; [ apply elem_of_union_r, elem_of_singleton_2; reflexivity | ].
                 eapply wt_act; [ | exact hq ].
                 eapply ParRight. eapply lts_multiset_add; eauto.
           ++ eapply NCM_wt_nil_inv in w as [-> | [hp | hq]].
              ** rewrite (union_difference_L
                    {[(g 𝟘 ‖ p) ▷ m; (g 𝟘 ‖ q) ▷ m]} X').
                 --- eapply coin_union_l. eapply CIH.
                 --- intros z hz. apply elem_of_union in hz as [hz | hz];
                       apply elem_of_singleton_1 in hz; subst z.
                     +++ eapply hX2; [ apply elem_of_union_l, elem_of_singleton_2; reflexivity | ].
                         eapply wt_act; [ | eapply wt_nil ].
                         eapply ParRight. eapply lts_multiset_minus; eauto.
                     +++ eapply hX2; [ apply elem_of_union_r, elem_of_singleton_2; reflexivity | ].
                         eapply wt_act; [ | eapply wt_nil ].
                         eapply ParRight. eapply lts_multiset_minus; eauto.
              ** eapply coin_elem_of.
                 eapply hX2; [ apply elem_of_union_l, elem_of_singleton_2; reflexivity | ].
                 eapply wt_act; [ | exact hp ].
                 eapply ParRight. eapply lts_multiset_minus; eauto.
              ** eapply coin_elem_of.
                 eapply hX2; [ apply elem_of_union_r, elem_of_singleton_2; reflexivity | ].
                 eapply wt_act; [ | exact hq ].
                 eapply ParRight. eapply lts_multiset_minus; eauto.
    + intros hX.
      eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      constructor. intros t Ht.
      eapply NCM_tau_inv in Ht as [-> | ->].
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_l, elem_of_singleton_2; reflexivity.
      * eapply termination_if_termination_set_helper; eauto.
        apply elem_of_union_r, elem_of_singleton_2; reflexivity.
Qed.

Example code_hoisting_outputs (M : MO (ExtAct TypeOfActions)) :
  ({[ GL ▷ M ]} : gset (proc * MO (ExtAct TypeOfActions)))
    ᶜᵒ≼ₜₒᵥᵥₑᵣ ({[ (Wo ‖ C) ▷ M ]} : gset (proc * MO (ExtAct TypeOfActions))).
Proof.
  unfold copre. eapply gfp_prop. intros PRE. revert M. revert PRE.
  apply (tower (P := fun R => forall M,
    R ({[ GL ▷ M ]} : gset (proc * MO (ExtAct TypeOfActions)))
      {[ (Wo ‖ C) ▷ M ]})).
  - intros S HS M R HR. eapply HS; eauto.
  - intros PRE CIH M.
    constructor.
    + intros Y' hY'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        eapply WCM_wt_nil_inv in hw as [-> | [hp | hq]].
        -- eapply CIH.
        -- eapply coin_wt_nil_singleton.
           eapply wt_tau; [ eapply ParLeft, gl_to_wp | exact hp ].
        -- eapply coin_wt_nil_singleton.
           eapply wt_tau; [ eapply ParLeft, gl_to_wq | exact hq ].
    + intros hX y mem hst. exfalso.
      apply elem_of_singleton_1 in mem; subst y.
      eapply (lts_refuses_spec2 ((Wo ‖ C) ▷ M) τ);
        [ eexists; eapply ParLeft, lts_parR, lts_choiceL; constructor | exact hst ].
    + intros μ Y' X' hcnv hY' hX'. revert hY'.
      induction Y' using set_ind_L; intros hY'.
      * eapply empty_is_a_top_element.
      * eapply wt_set_from_pset_spec1_union_rev_l in hY' as h_x.
        eapply wt_set_from_pset_spec1_union_rev_r in hY' as h_rest.
        eapply coin_union_right; eauto.
        destruct (h_x x) as (y & mem & hw); [apply elem_of_singleton_2; reflexivity|].
        apply elem_of_singleton_1 in mem; subst y.
        destruct hX' as (hX1 & hX2).
        inversion hw; subst.
        -- eapply WCM_tau_inv in l as [-> | ->].
           ++ eapply coin_elem_of. eapply hX2.
              { apply elem_of_singleton_2; reflexivity. }
              eapply wt_tau; [ eapply ParLeft, gl_to_wp | eauto ].
           ++ eapply coin_elem_of. eapply hX2.
              { apply elem_of_singleton_2; reflexivity. }
              eapply wt_tau; [ eapply ParLeft, gl_to_wq | eauto ].
        -- eapply WCM_mu_inv in l
             as [ (-> & ->) | [ (η & hduo & hnb & ->) | (m & hnb & -> & ->) ] ].
           ++ eapply NCM_wt_nil_inv in w as [-> | [hp | hq]].
              ** rewrite (union_difference_L
                    {[(g 𝟘 ‖ p) ▷ M; (g 𝟘 ‖ q) ▷ M]} X').
                 --- eapply coin_union_l. eapply nchoice_copre_rev_fw.
                 --- intros z hz. apply elem_of_union in hz as [hz | hz];
                       apply elem_of_singleton_1 in hz; subst z.
                     +++ eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
                         eapply wt_tau; [ eapply ParLeft, gl_to_wp | ].
                         eapply wt_act; [ eapply ParLeft, wp_fire | eapply wt_nil ].
                     +++ eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
                         eapply wt_tau; [ eapply ParLeft, gl_to_wq | ].
                         eapply wt_act; [ eapply ParLeft, wp_fire | eapply wt_nil ].
              ** eapply coin_elem_of. eapply hX2.
                 { apply elem_of_singleton_2; reflexivity. }
                 eapply wt_tau; [ eapply ParLeft, gl_to_wp | ].
                 eapply wt_act; [ eapply ParLeft, wp_fire | exact hp ].
              ** eapply coin_elem_of. eapply hX2.
                 { apply elem_of_singleton_2; reflexivity. }
                 eapply wt_tau; [ eapply ParLeft, gl_to_wq | ].
                 eapply wt_act; [ eapply ParLeft, wp_fire | exact hq ].
           ++ eapply WCM_wt_nil_inv in w as [-> | [hp | hq]].
              ** rewrite (union_difference_singleton_L (GL ▷ ({[+ η +]} ⊎ M)) X').
                 --- eapply coin_union_l. eapply CIH.
                 --- eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
                     eapply wt_act; [ | eapply wt_nil ].
                     eapply ParRight. eapply lts_multiset_add; eauto.
              ** eapply coin_elem_of. eapply hX2.
                 { apply elem_of_singleton_2; reflexivity. }
                 eapply wt_act; [ eapply ParRight; eapply lts_multiset_add; eauto | ].
                 eapply wt_tau; [ eapply ParLeft, gl_to_wp | exact hp ].
              ** eapply coin_elem_of. eapply hX2.
                 { apply elem_of_singleton_2; reflexivity. }
                 eapply wt_act; [ eapply ParRight; eapply lts_multiset_add; eauto | ].
                 eapply wt_tau; [ eapply ParLeft, gl_to_wq | exact hq ].
           ++ eapply WCM_wt_nil_inv in w as [-> | [hp | hq]].
              ** rewrite (union_difference_singleton_L (GL ▷ m) X').
                 --- eapply coin_union_l. eapply CIH.
                 --- eapply hX2; [ apply elem_of_singleton_2; reflexivity | ].
                     eapply wt_act; [ | eapply wt_nil ].
                     eapply ParRight. eapply lts_multiset_minus; eauto.
              ** eapply coin_elem_of. eapply hX2.
                 { apply elem_of_singleton_2; reflexivity. }
                 eapply wt_act; [ eapply ParRight; eapply lts_multiset_minus; eauto | ].
                 eapply wt_tau; [ eapply ParLeft, gl_to_wp | exact hp ].
              ** eapply coin_elem_of. eapply hX2.
                 { apply elem_of_singleton_2; reflexivity. }
                 eapply wt_act; [ eapply ParRight; eapply lts_multiset_minus; eauto | ].
                 eapply wt_tau; [ eapply ParLeft, gl_to_wq | exact hq ].
    + intros hX.
      eapply termination_set_for_all. intros y mem.
      apply elem_of_singleton_1 in mem; subst y.
      assert ((GL ▷ M) ⤓) as hGL.
      { eapply termination_if_termination_set_helper; eauto.
        apply elem_of_singleton_2; reflexivity. }
      destruct hGL as [hGL].
      constructor. intros t Ht.
      eapply WCM_tau_inv in Ht as [-> | ->].
      * eapply hGL. eapply ParLeft, gl_to_wp.
      * eapply hGL. eapply ParLeft, gl_to_wq.
Qed.

End Code_Hoisting_FW.
