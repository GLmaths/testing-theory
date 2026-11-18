(* begin hide *)
(*
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
(* begin hide *)
(* * lqCCS: soundness of the alternative preorder

    A tested program [⟨ρ, (P, T)⟩], for an observer [T], runs in step with a
    component [(n, (P, C))] of [𝔻] weighted by [ρ]: the observer is in the
    state [T'] reached from [T] by the co-trace [n] followed by the consumed
    outputs [C], the real program is [P ∥ T'].  Related distributions have
    the same successful mass, every scheduled step of one is a scheduled
    step of the other (a choice of the program on one side is the same
    choice on the other; a synchronisation with the observer, or an action
    of the observer on the memory, is the instruction tagged by the observer),
    and one is stable iff the other is.  The runs transfer in both
    directions ([run_transfer]), so a witness run in [𝔻] given by [≼] is
    a witness run of the tested programs: [≼] is below the Smyth must for
    the observers. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list propset.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer.
From TestingTheory Require Import lqCCS.quantum_mem.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper_substitution.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper_substitution.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper_substitution.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Rec_Observers.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Lists *)

Section LqP.
  Context `{LP : lqCCS_Parameters}.

Lemma Forall2_concat' {A B} (R : A → B → Prop) (ls : list (list A)) (ks : list (list B)) :
  Forall2 (Forall2 R) ls ks → Forall2 R (concat ls) (concat ks).
Proof. induction 1; simpl; [constructor|]. by apply Forall2_app. Qed.

Lemma dmass_of_cons' `{Weights} {C} (good : C → Prop) `{∀ c, Decision (good c)} x (Δ : dist C) :
  dmass_of good (x :: Δ)
  = if decide (good x.1) then prob_add (mass x.2) (dmass_of good Δ) else dmass_of good Δ.
Proof. done. Qed.

Definition off_tag (o : offer) : tag :=
  match o with OffOut k _ _ | OffIn k _ | OffOp k _ _ | OffMeas k _ _ | OffInit k _ | OffUnfold k => k end.

Definition off_kind (o : offer) : okind :=
  match o with
  | OffOut _ _ _ => KOut | OffIn _ _ => KIn | OffOp _ _ _ => KOp | OffMeas _ _ _ => KMeas | OffInit _ _ => KInit
  | OffUnfold _ => KRec
  end.

Lemma menu_kind T : observer T → ∀ n o, menu T n o → (off_tag o, off_kind o) ∈ tagged T.
Proof.
  intros HT n o (T' & a & HT' & <- & Hne).
  destruct (co_succ T' a) as [|T'' l] eqn:E; [done|].
  assert (Hin : (co_tag a, kind_of a) ∈ tagged T').
  { apply (co_succ_tagged T' a T''). rewrite E. by left. }
  assert (Hsub : tagged T' `sublist_of` tagged T) by (by eapply tnodes_tags; [apply HT|]).
  pose proof (elem_of_submseteq _ _ _ Hin (sublist_submseteq _ _ Hsub)) as Hin'.
  by destruct a.
Qed.

Section Sound.
  Context `{QM : QuantumModel}.
  Context (T : proc) (TG : tag → okind → Prop) (HW : wobserver T).
  Context (Htag : ∀ n T' k x, T' ∈ tnodes T n → (k, x) ∈ tagged T' → TG k x).
  Context (Huniq : ∀ k x y, TG k x → TG k y → x = y).
  Context (L : lifting).

  Definition tgT : propset tag := {[ t | ∃ x, TG t x ]}.

  Notation I := (menu T).
  Notation S := (S_T T).
  Notation comp := (node * (proc * list msg))%type.
  Notation dcstep := (cstep (menu T) (O_T T)).


  (* ** Programs under test: tags apart from those of the observer *)

  Definition prog_ok (P : proc) : Prop := ∀ t, t ∈ otags P → t ∉ tgT.

  Lemma prog_ok_step P s l P' : prog_ok P → P ⟶ₚ{l}[s] P' → prog_ok P'.
  Proof.
    intros Ht Hp t Ht'. apply Ht. by eapply prog_step_otags.
  Qed.

  Lemma prog_ok_choice P s l P' t :
    prog_ok P → P ⟶ₚ{l}[s] P' → t ∈ s → t ∉ tgT.
  Proof. intros Ht Hp Hs. apply Ht, tags_otags. by eapply prog_step_choice_tags. Qed.

  (* ** The relation between a tested program and a component of 𝔻 *)

  Definition rel_par (x : proc * St) (y : comp * St) : Prop :=
    x.2 = y.2 ∧ prog_ok y.1.2.1 ∧
    ∃ T', T' ∈ tnodes T (eff y.1.1 y.1.2.2) ∧ x.1 = y.1.2.1 ∥ T'.

  Definition rel_comp (x : proc * proc * St) (y : comp * St) : Prop := rel_par (par_of x.1, x.2) y.

  Definition Rel (Δ : dist (proc * proc)) (Θ : dist comp) : Prop := Forall2 rel_comp Δ Θ.

  Lemma rel_dmap Δ Θ : Forall2 rel_par (dmap par_of Δ) Θ ↔ Forall2 rel_comp Δ Θ.
  Proof.
    split.
    - revert Θ. induction Δ as [|x Δ IH]; intros Θ HF; inversion HF; subst; constructor; [done|by apply IH].
    - induction 1; simpl; by constructor.
  Qed.

  Lemma rel_unpar Δ Θ : Forall2 rel_par Δ Θ → ∃ Δx, Δ = dmap par_of Δx ∧ Forall2 rel_comp Δx Θ.
  Proof.
    induction 1 as [|x y Δ Θ Hxy _ (Δx & -> & HF)]; [by exists []|].
    destruct x as [R ρ]. pose proof Hxy as (_ & _ & T' & _ & E). simpl in E. subst R.
    exists (((y.1.2.1, T'), ρ) :: Δx). split; [done|]. by constructor.
  Qed.

  (* ** Facts on the effective node *)

  Lemma eff_app n C m : eff n (C ++ [m]) = eff n C ++ [co_of_msg m].
  Proof. unfold eff. by rewrite fmap_app, app_assoc. Qed.

  Lemma eff_obs n C T' : T' ∈ tnodes T (eff n C) → obsr T'.
  Proof. apply HW. Qed.

  Lemma succ_vis T' a T'' : T'' ∈ co_succ T' a → T' ⟶ₚ{co_act a}[{[+ co_tag a +]}] T''.
  Proof. apply co_succ_step. Qed.

  Lemma eff_successb n C T' :
    T' ∈ tnodes T (eff n C) → ∃ Tn, Tn ∈ tnodes T n ∧ successb T' = successb Tn.
  Proof.
    unfold eff. revert T'. induction C as [|m C IH] using rev_ind; intros T' HT'.
    - simpl in HT'. rewrite app_nil_r in HT'. by exists T'.
    - rewrite fmap_app, app_assoc in HT'. simpl in HT'.
      apply tnodes_app_elem in HT' as (T0 & HT0 & Hz0).
      destruct (IH _ HT0) as (Tn & HTn & E). exists Tn. split; [done|].
      rewrite <- E. by eapply co_succ_out_successb.
  Qed.

  (* A co-action enabled before the consumed outputs, and not one of them, stays enabled. *)
  Lemma eff_keep n C b Tn T' :
    Tn ∈ tnodes T n → T' ∈ tnodes T (eff n C) → co_succ Tn b ≠ [] →
    (∀ m, m ∈ C → ∀ c' v', b ≠ CoOut m.1.1 c' v') → co_succ T' b ≠ [].
  Proof.
    intros HTn. unfold eff. revert T'. induction C as [|m C IH] using rev_ind; intros T' HT' Hne Hb.
    - simpl in HT'. rewrite app_nil_r in HT'. by rewrite (tnodes_unique_w T n T' Tn HW HT' HTn).
    - rewrite fmap_app, app_assoc in HT'. simpl in HT'.
      apply tnodes_app_elem in HT' as (T0 & HT0 & Hz0).
      apply (co_succ_out_keep T0 _ _ _ _ _ Hz0).
      + apply IH; [done|done|]. intros m' Hm'. apply Hb. apply elem_of_app. by left.
      + apply Hb. apply elem_of_app. right. by left.
  Qed.

  (* A consumed output is not offered again. *)
  Lemma eff_out_gone n C m c' v' T' :
    T' ∈ tnodes T (eff n C) → m ∈ C → co_succ T' (CoOut m.1.1 c' v') = [].
  Proof.
    intros HT' Hm. apply list_elem_of_split in Hm as (C1 & C2 & ->).
    apply (proj2 (proj2 HW) (n ++ (co_of_msg <$> C1)) (co_of_msg <$> C2) m.1.1 m.1.2 m.2).
    unfold eff in HT'. rewrite fmap_app, fmap_cons in HT'. by rewrite <- app_assoc.
  Qed.

  (* The menu at the visible node contains the offers answered after the consumptions. *)
  Lemma eff_menu n C a T' T'' :
    T' ∈ tnodes T (eff n C) → T'' ∈ co_succ T' a →
    I n (offer_of a) ∧ T'' ∈ tnodes T (eff (n ++ [a]) C).
  Proof.
    intros HT' H''. destruct (eff_swap T n C a T' T'' HT' H'') as (Tn & Tb & HTn & HTb & HT'').
    split; [|done]. exists Tn, a. split; [done|]. split; [done|]. intros E. rewrite E in HTb.
    by apply elem_of_nil in HTb.
  Qed.

  (* ** Success and masses *)

  Lemma rel_success x y : rel_comp x y → success x.1.2 ↔ S y.1.1 = true.
  Proof.
    intros (_ & _ & T' & HT' & E). destruct x as [[P0 T0] ρ0]. simpl in E. injection E as _ ->. simpl.
    unfold success. destruct (eff_successb _ _ _ HT') as (Tn & HTn & E). rewrite E.
    symmetry. apply (S_T_tnodes_w T _ Tn HW HTn).
  Qed.

  Lemma rel_mass Δ Θ :
    Rel Δ Θ → dmass_of (λ c : proc * proc, success c.2) Δ = dmass_of (λ x : comp, S x.1 = true) Θ.
  Proof.
    induction 1 as [|x y Δ Θ Hxy _ IH]; [done|].
    unfold dmass_of in *. cbn [foldr]. rewrite IH. pose proof (rel_success x y Hxy) as Hs. destruct Hxy as (Hρ & _).
    destruct x as [Rx ρx]; destruct y as [cy ρy]; simpl in *; subst ρy.
    case_decide as Hx; case_decide as Hy; [done|exfalso; by apply Hy, Hs|exfalso; by apply Hx, Hs|done].
  Qed.

  (* ** Kinds of the tags of the observer *)

  Lemma menu_kind_g n o : I n o → TG (off_tag o) (off_kind o).
  Proof.
    intros (T' & a & HT' & <- & Hne).
    destruct (co_succ T' a) as [|T'' l] eqn:E; [done|].
    assert (Hin : (co_tag a, kind_of a) ∈ tagged T').
    { apply (co_succ_tagged T' a T''). rewrite E. by left. }
    pose proof (Htag _ _ _ _ HT' Hin) as Hin'.
    by destruct a.
  Qed.

  Lemma tag_kind_unique k x y : TG k (x) → TG k (y) → x = y.
  Proof. exact (Huniq k x y). Qed.

  Lemma tag_in_T k x : TG k (x) → k ∈ tgT.
  Proof. intros Hk. apply elem_of_PropSet. by exists x. Qed.

  Definition mem_kind (x : okind) : Prop := x = KOp ∨ x = KMeas ∨ x = KInit ∨ x = KRec.

  (* ** Correspondence between the choices of the tested program and the items of 𝔻 *)

  Inductive corr : choice → item → Prop :=
  | corr_ch σ : (∀ t x, t ∈ σ → TG t (x) → x = KOut) → corr σ (ICh σ)
  | corr_mem k t x : TG k (x) → mem_kind x → corr ({[+ k +]}) (IOff k t)
  | corr_chan k t : TG k (KIn) → t ∉ tgT → corr {[+ t; k +]} (IOff k t).

  Lemma corr_prog P s l P' : prog_ok P → P ⟶ₚ{l}[s] P' → corr s (ICh s).
  Proof.
    intros Hok Hp. apply corr_ch. intros u x Hu Hx. exfalso.
    apply (prog_ok_choice P s l P' u Hok Hp Hu). by eapply tag_in_T.
  Qed.

  Lemma corr_cons t k : t ∉ tgT → TG k (KOut) → corr {[+ t; k +]} (ICh {[+ t; k +]}).
  Proof.
    intros Ht Hk. apply corr_ch. intros u x Hu Hx.
    destruct (choice_pair_elem u t k Hu) as [-> | ->]; [exfalso; apply Ht; by eapply tag_in_T|].
    exact (tag_kind_unique k x KOut Hx Hk).
  Qed.

  (* A visible step of a parallel composition is a step of one side. *)
  Lemma par_ext_inv P Q s α R' :
    (P ∥ Q) ⟶ₚ{ActExt α}[s] R' →
    (∃ P', P ⟶ₚ{ActExt α}[s] P' ∧ R' = P' ∥ Q) ∨ (∃ Q', Q ⟶ₚ{ActExt α}[s] Q' ∧ R' = P ∥ Q').
  Proof. inversion 1; subst; eauto. Qed.

  Lemma par_tau_inv P Q s R' :
    (P ∥ Q) ⟶ₚ{τ}[s] R' →
    (∃ P', P ⟶ₚ{τ}[s] P' ∧ R' = P' ∥ Q) ∨ (∃ Q', Q ⟶ₚ{τ}[s] Q' ∧ R' = P ∥ Q')
    ∨ (∃ t t' c v P' Q', s = {[+ t; t' +]} ∧ R' = P' ∥ Q' ∧
        P ⟶ₚ{c ! v}[{[+ t +]}] P' ∧ Q ⟶ₚ{c ? v}[{[+ t' +]}] Q')
    ∨ (∃ t t' c v P' Q', s = {[+ t; t' +]} ∧ R' = P' ∥ Q' ∧
        P ⟶ₚ{c ? v}[{[+ t +]}] P' ∧ Q ⟶ₚ{c ! v}[{[+ t' +]}] Q').
  Proof. inversion 1; subst; eauto 20. Qed.

  Lemma choice_pair_elem_in t t' : t ∈ ({[+ t; t' +]} : choice) ∧ t' ∈ ({[+ t; t' +]} : choice).
  Proof. rewrite !gmultiset_elem_of_disj_union, !gmultiset_elem_of_singleton. auto. Qed.

  (* The pair of a tag of the program and a tag of the observer determines both. *)
  Lemma choice_pair_inv t k t' k' :
    t ∉ tgT → k ∈ tgT → t' ∉ tgT → k' ∈ tgT → ({[+ t; k +]} : choice) = {[+ t'; k' +]} → t = t' ∧ k = k'.
  Proof.
    intros Ht Hk Ht' Hk' E. apply choice_pair_eq in E as [?|[-> ->]]; [done|]. by exfalso; apply Ht.
  Qed.

  Lemma co_act_in_inv a k c v : co_tag a = k → co_act a = c ? v → a = CoIn k c v.
  Proof. destruct a; simpl; intros; simplify_eq; done. Qed.
  Lemma co_act_out_inv a k c v : co_tag a = k → co_act a = c ! v → a = CoOut k c v.
  Proof. destruct a; simpl; intros; simplify_eq; done. Qed.
  Lemma co_act_op_inv a k U qs : co_tag a = k → co_act a = ⦅qs⦆ ! U → a = CoOp k U qs.
  Proof. destruct a; simpl; intros; simplify_eq; done. Qed.
  Lemma co_act_init_inv a k q : co_tag a = k → co_act a = reinit q → a = CoInit k q.
  Proof. destruct a; simpl; intros; simplify_eq; done. Qed.
  Lemma co_act_meas_inv a k M qs m : co_tag a = k → co_act a = M ⦅qs⦆? m → a = CoMeas k M qs m.
  Proof. destruct a; simpl; intros; simplify_eq; done. Qed.

  (* A step of the observer, with its co-action. *)
  Lemma obs_step_co n C T' k α T'' :
    T' ∈ tnodes T (eff n C) → T' ⟶ₚ{ActExt α}[{[+ k +]}] T'' →
    ∃ a, co_tag a = k ∧ co_act a = ActExt α ∧ T'' ∈ co_succ T' a ∧ TG k (kind_of a).
  Proof.
    intros HT' Hs. destruct (co_succ_complete_r T' k α T'' (proj1 (eff_obs _ _ _ HT')) Hs) as (a & Hk & Hα & Hin).
    exists a. split; [done|]. split; [done|]. split; [done|]. rewrite <- Hk.
    eapply Htag; [exact HT'|by eapply co_succ_tagged].
  Qed.

  Lemma Forall2_head {A B} (Q : A → B → Prop) (l1 : list A) (l2 : list B) :
    Forall2 Q l1 l2 → l1 ≠ [] → ∃ x y, Q x y.
  Proof. destruct 1; [done|]. intros _. eauto. Qed.

  (* The outcomes of a measurement are all on the side of the program, or all on
      the side of the observer. *)
  Lemma meas_side_P P T' t M qs (ks : list (nat)) Rs :
    t ∉ tags T' →
    Forall2 (λ k' R', (P ∥ T') ⟶ₚ{M ⦅qs⦆? k'}[{[+ t +]}] R') ks Rs →
    ∃ Ps, Forall2 (λ k' P', P ⟶ₚ{M ⦅qs⦆? k'}[{[+ t +]}] P') ks Ps
      ∧ Rs = (λ P', P' ∥ T') <$> Ps.
  Proof.
    intros Ht. induction 1 as [|k' R' ks Rs Hp _ (Ps & HPs & ->)]; [by exists []|].
    apply par_ext_inv in Hp as [(P' & Hp & ->)|(T'' & Hp & ->)].
    - exists (P' :: Ps). split; [by constructor|done].
    - exfalso. apply Ht. eapply prog_step_choice_tags; [exact Hp|by apply gmultiset_elem_of_singleton].
  Qed.

  Lemma meas_side_T P T' t M qs (ks : list (nat)) Rs :
    t ∉ tags P →
    Forall2 (λ k' R', (P ∥ T') ⟶ₚ{M ⦅qs⦆? k'}[{[+ t +]}] R') ks Rs →
    ∃ Ts, Forall2 (λ k' T'', T' ⟶ₚ{M ⦅qs⦆? k'}[{[+ t +]}] T'') ks Ts
      ∧ Rs = (λ T'', P ∥ T'') <$> Ts.
  Proof.
    intros Ht. induction 1 as [|k' R' ks Rs Hp _ (Ts & HTs & ->)]; [by exists []|].
    apply par_ext_inv in Hp as [(P' & Hp & ->)|(T'' & Hp & ->)].
    - exfalso. apply Ht. eapply prog_step_choice_tags; [exact Hp|by apply gmultiset_elem_of_singleton].
    - exists (T'' :: Ts). split; [by constructor|done].
  Qed.

  (* The step of a component of the tested program is a step of the component of 𝔻. *)
  Lemma par_fwd ρ n P C T' σ Δ :
    prog_ok P → T' ∈ tnodes T (eff n C) → sched_step ρ (P ∥ T') σ Δ →
    ∃ it, corr σ it ∧ ∀ it', corr σ it' →
      ∃ Θc, dcstep ρ (n, (P, C)) it' Θc ∧ Forall2 rel_par Δ Θc.
  Proof.
    intros Hok HT' Hs.
    (* a choice of the program only *)
    assert (Hch : ∀ s l P', P ⟶ₚ{l}[s] P' → ∀ it', corr s it' → it' = ICh s).
    { intros s l P' Hp it' Hc. inversion Hc as [? Hno|k ? ? Hk' Hx'|k ? Hk' Ht']; subst; [done| |].
      - exfalso. apply (prog_ok_choice P _ _ _ k Hok Hp); [by apply gmultiset_elem_of_singleton|]. by eapply tag_in_T.
      - exfalso. apply (prog_ok_choice P _ _ _ k Hok Hp); [apply choice_pair_elem_in|]. by eapply tag_in_T. }
    (* the item of a memory action of the observer *)
    assert (Hmem : ∀ k x, TG k (x) → mem_kind x →
      ∀ it', corr ({[+ k +]}) it' → ∃ t', it' = IOff k t').
    { intros k x Hk Hx it' Hc. remember {[+ k +]} as σ0 eqn:U in Hc.
      destruct Hc as [σ1 Hno|k0 t0 x0 Hk0 Hx0|k0 t0 Hk0 Ht0]; subst.
      - exfalso. rewrite (Hno k x ltac:(by apply gmultiset_elem_of_singleton) Hk) in Hx. by destruct Hx as [?|[?|[?|?]]].
      - apply choice_tag_inj in U as ->. by eexists.
      - by apply choice_pair_neq_tag in U. }
    (* the item of an input of the observer *)
    assert (Hsync : ∀ t k, t ∉ tgT → TG k (KIn) →
      ∀ it', corr {[+ t; k +]} it' → it' = IOff k t).
    { intros t k Ht Hk it' Hc. remember {[+ t; k +]} as σ0 eqn:U in Hc.
      destruct Hc as [σ1 Hno|k0 t0 x0 Hk0 Hx0|k0 t0 Hk' Ht']; subst.
      - exfalso. by pose proof (Hno k KIn (proj2 (choice_pair_elem_in t k)) Hk).
      - symmetry in U. by apply choice_pair_neq_tag in U.
      - apply choice_pair_eq in U as [[-> ->]|[-> ->]]; [done|]. exfalso. apply Ht. by eapply tag_in_T. }
    (* the item of a consumption of an output of the observer *)
    assert (Hcons : ∀ t k, t ∉ tgT → TG k (KOut) →
      ∀ it', corr {[+ t; k +]} it' → it' = ICh {[+ t; k +]}).
    { intros t k Ht Hk it' Hc. remember {[+ t; k +]} as σ0 eqn:U in Hc.
      destruct Hc as [σ1 Hno|k0 t0 x0 Hk0 Hx0|k0 t0 Hk' Ht']; subst; [done| |].
      - symmetry in U. by apply choice_pair_neq_tag in U.
      - apply choice_pair_eq in U as [[-> ->]|[-> ->]]; [by pose proof (tag_kind_unique _ _ _ Hk Hk')|].
        exfalso. apply Ht. by eapply tag_in_T. }
    inversion Hs as [R' Hp|U qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 Hf]; subst.
    - (* a silent step *)
      apply par_tau_inv in Hp as [(P' & Hp & ->)|[(T'' & Hp & ->)|[(t & k & c & v & P' & T'' & -> & -> & Hp & Hq)|(t & k & c & v & P' & T'' & -> & -> & Hp & Hq)]]].
      + exists (ICh σ). split; [exact (corr_prog _ _ _ _ Hok Hp)|].
        intros it' Hc. rewrite (Hch _ _ _ Hp _ Hc). eexists. split; [apply cs_ch; by apply ss_tau|].
        simpl. constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + (* the observer unfolds a recursion *)
        destruct (obs_tau_r T' σ T'' (eff_obs _ _ _ HT') Hp) as (k & -> & Hin).
        destruct (eff_menu n C _ T' T'' HT' Hin) as (HI & HT''). simpl in HI.
        assert (Hkind : TG k KRec).
        { eapply Htag; [exact HT'|]. exact (co_succ_tagged T' (CoUnfold k) T'' Hin). }
        exists (IOff k 0). split; [eapply corr_mem; [exact Hkind|right; right; by right]|].
        intros it' Hc. destruct (Hmem k KRec Hkind ltac:(right; right; by right) _ Hc) as (t' & ->).
        eexists. split; [by apply cs_unfold|].
        constructor; [|constructor]. split; [done|]. split; [done|]. by exists T''.
      + (* the program outputs, the observer inputs *)
        destruct (obs_step_co n C T' k _ T'' HT' Hq) as (a & Hk & Hα & Hin & Hkind).
        rewrite (co_act_in_inv a k c v Hk Hα) in Hin, Hkind. simpl in Hkind.
        destruct (eff_menu n C _ T' T'' HT' Hin) as (HI & HT''). simpl in HI.
        assert (Ht : t ∉ tgT) by (eapply prog_ok_choice; [done|exact Hp|by apply gmultiset_elem_of_singleton]).
        exists (IOff k t). split; [by apply corr_chan|].
        intros it' Hc. rewrite (Hsync t k Ht Hkind _ Hc).
        eexists. split; [by apply cs_in|].
        constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T''.
      + (* the program inputs, the observer outputs *)
        destruct (obs_step_co n C T' k _ T'' HT' Hq) as (a & Hk & Hα & Hin & Hkind).
        rewrite (co_act_out_inv a k c v Hk Hα) in Hin, Hkind. simpl in Hkind.
        destruct (eff_swap T n C _ T' T'' HT' Hin) as (Tn & Tb & HTn & HTb & _).
        assert (HE : (k, c, v) ∈ O_T T n).
        { apply O_T_spec. exists Tn. split; [done|]. intros U. rewrite U in HTb. by apply elem_of_nil in HTb. }
        assert (Ht : t ∉ tgT) by (eapply prog_ok_choice; [done|exact Hp|by apply gmultiset_elem_of_singleton]).
        assert (HkC : k ∉ (λ m : msg, m.1.1) <$> C).
        { intros (m & Hm & HmC)%list_elem_of_fmap. simpl in Hm. rewrite Hm, (eff_out_gone n C m c v T' HT' HmC) in Hin.
          by apply elem_of_nil in Hin. }
        exists (ICh {[+ t; k +]}). split; [by apply corr_cons|].
        intros it' Hc. rewrite (Hcons t k Ht Hkind _ Hc).
        eexists. split; [by eapply cs_recv|].
        constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|].
        exists T''. split; [|done]. simpl. rewrite eff_app. apply tnodes_app_elem. by exists T'.
    - (* an operation on the memory *)
      apply par_ext_inv in Hp as [(P' & Hp & ->)|(T'' & Hp & ->)].
      + exists (ICh σ). split; [exact (corr_prog _ _ _ _ Hok Hp)|].
        intros it' Hc. rewrite (Hch _ _ _ Hp _ Hc). eexists. split; [apply cs_ch; by apply ss_op|].
        simpl. constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + destruct (prog_step_ext_choice _ _ _ _ Hp) as (k & ->).
        destruct (obs_step_co n C T' k _ T'' HT' Hp) as (a & Hk & Hα & Hin & Hkind).
        rewrite (co_act_op_inv a k U qs Hk Hα) in Hin, Hkind. simpl in Hkind.
        destruct (eff_menu n C _ T' T'' HT' Hin) as (HI & HT''). simpl in HI.
        exists (IOff k 0). split; [eapply corr_mem; [exact Hkind|by left]|].
        intros it' Hc. destruct (Hmem k KOp Hkind ltac:(by left) _ Hc) as (t' & ->).
        eexists. split; [by apply cs_op|].
        constructor; [|constructor]. split; [done|]. split; [done|]. by exists T''.
    - (* an initialisation *)
      apply par_ext_inv in Hp as [(P' & Hp & ->)|(T'' & Hp & ->)].
      + exists (ICh σ). split; [exact (corr_prog _ _ _ _ Hok Hp)|].
        intros it' Hc. rewrite (Hch _ _ _ Hp _ Hc). eexists. split; [apply cs_ch; by apply ss_init|].
        simpl. constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + destruct (prog_step_ext_choice _ _ _ _ Hp) as (k & ->).
        destruct (obs_step_co n C T' k _ T'' HT' Hp) as (a & Hk & Hα & Hin & Hkind).
        rewrite (co_act_init_inv a k qs Hk Hα) in Hin, Hkind. simpl in Hkind.
        destruct (eff_menu n C _ T' T'' HT' Hin) as (HI & HT''). simpl in HI.
        exists (IOff k 0). split; [eapply corr_mem; [exact Hkind|right; right; by left]|].
        intros it' Hc. destruct (Hmem k KInit Hkind ltac:(right; right; by left) _ Hc) as (t' & ->).
        eexists. split; [by apply cs_init|].
        constructor; [|constructor]. split; [done|]. split; [done|]. by exists T''.
    - (* a measurement: all the outcomes are on the same side *)
      destruct (prog_step_ext_choice _ _ _ _ Hp0) as (t & ->).
      apply par_ext_inv in Hp0 as [(P0 & Hp0 & _)|(T0 & Hp0 & _)].
      + (* the program measures *)
        assert (Ht : t ∉ tgT) by (eapply prog_ok_choice; [done|exact Hp0|by apply gmultiset_elem_of_singleton]).
        assert (Ht' : t ∉ tags T').
        { intros Hin. apply Ht. unfold tags in Hin. apply list_elem_of_fmap in Hin as ([t0 x] & -> & Hin).
          exact (tag_in_T _ _ (Htag _ _ _ _ HT' Hin)). }
        destruct (meas_side_P P T' t M qs _ _ Ht' Hf) as (Ps & HPs & ->).
        exists (ICh ({[+ t +]})). split; [exact (corr_prog _ _ _ _ Hok Hp0)|].
        intros it' Hc. rewrite (Hch _ _ _ Hp0 _ Hc). eexists. split; [apply cs_ch; by eapply ss_meas|].
        rewrite zip_with_fmap_r. clear Hf Hp0 Hs. revert HPs. generalize (outs_nz (meas_of M qs) ρ) as ks.
        intros ks HPs. induction HPs as [|k' P' ks Ps Hp _ IH]; simpl; [constructor|].
        constructor; [|done]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + (* the observer measures *)
        destruct (obs_step_co n C T' t _ T0 HT' Hp0) as (a & Hk & Hα & Hin & Hkind).
        rewrite (co_act_meas_inv a t M qs 0 Hk Hα) in Hin, Hkind. simpl in Hkind.
        destruct (eff_menu n C _ T' T0 HT' Hin) as (HI & _). simpl in HI.
        assert (HtP : t ∉ tags P) by (intros HtP; apply (Hok t (tags_otags P t HtP)); by eapply tag_in_T).
        destruct (meas_side_T P T' t M qs _ _ HtP Hf) as (Ts & HTs & ->).
        exists (IOff t 0). split; [eapply corr_mem; [exact Hkind|right; by left]|].
        intros it' Hc. destruct (Hmem t KMeas Hkind ltac:(right; by left) _ Hc) as (t' & ->).
        eexists. split; [by apply cs_meas|].
        rewrite zip_with_fmap_r. clear Hf Hp0 Hs Hin HI. revert HTs. generalize (outs_nz (meas_of M qs) ρ) as ks.
        intros ks HTs. induction HTs as [|k' T'' ks Ts Hq _ IH]; simpl; [constructor|].
        constructor; [|done]. split; [done|]. split; [done|].
        destruct (obs_step_co n C T' t _ T'' HT' Hq) as (a' & Hk' & Hα' & Hin' & _).
        rewrite (co_act_meas_inv a' t M qs k' Hk' Hα') in Hin'.
        destruct (eff_menu n C _ T' T'' HT' Hin') as (_ & HT''). by exists T''.
  Qed.

  (* ** From 𝔻 to the tested program *)

  Lemma offer_of_in a k c : offer_of a = OffIn k c → ∃ v, a = CoIn k c v.
  Proof. destruct a; simpl; intros; simplify_eq. by eexists. Qed.
  Lemma offer_of_op a k U qs : offer_of a = OffOp k U qs → a = CoOp k U qs.
  Proof. destruct a; simpl; intros; by simplify_eq. Qed.
  Lemma offer_of_meas a k M qs : offer_of a = OffMeas k M qs → ∃ m, a = CoMeas k M qs m.
  Proof. destruct a; simpl; intros; simplify_eq. by eexists. Qed.
  Lemma offer_of_init a k q : offer_of a = OffInit k q → a = CoInit k q.
  Proof. destruct a; simpl; intros; by simplify_eq. Qed.
  Lemma offer_of_unfold a k : offer_of a = OffUnfold k → a = CoUnfold k.
  Proof. destruct a; simpl; intros; by simplify_eq. Qed.

  Lemma hd_elem_of {A} (d : A) (l : list A) : l ≠ [] → hd d l ∈ l.
  Proof. destruct l; [done|]. intros _. by left. Qed.

  (* An offer of the menu is answered by the observer after the consumptions. *)
  Lemma menu_step_in n C T' k c v :
    T' ∈ tnodes T (eff n C) → I n (OffIn k c) →
    ∃ T'', T' ⟶ₚ{c ? v}[{[+ k +]}] T'' ∧ T'' ∈ tnodes T (eff (n ++ [CoIn k c v]) C).
  Proof.
    intros HT' (Tn & a & HTn & Ha & Hne). destruct (offer_of_in a k c Ha) as (v0 & ->).
    assert (Hne' : co_succ T' (CoIn k c v) ≠ []).
    { eapply eff_keep; [exact HTn|exact HT'|by eapply co_succ_in_val|]. by intros. }
    exists (hd 𝟘 (co_succ T' (CoIn k c v))). split; [apply (succ_vis T' (CoIn k c v)); by apply hd_elem_of|].
    by apply (eff_menu n C (CoIn k c v) T'), hd_elem_of.
  Qed.

  Lemma fmap_zip_with' {A B C D} (f : C → D) (g : A → B → C) (l : list A) (k : list B) :
    f <$> zip_with g l k = zip_with (λ x y, f (g x y)) l k.
  Proof. revert k. induction l as [|x l IH]; intros [|y k]; simpl; [done|done|done|]. by rewrite IH. Qed.

  (* An output offered at the node is answered by the observer after the consumptions. *)
  Lemma out_step n C T' k c v :
    T' ∈ tnodes T (eff n C) → (k, c, v) ∈ O_T T n → k ∉ (λ m : msg, m.1.1) <$> C →
    TG k (KOut) ∧
    ∃ T'', T' ⟶ₚ{c ! v}[{[+ k +]}] T'' ∧ T'' ∈ tnodes T (eff n (C ++ [(k, c, v)])).
  Proof.
    intros HT' (Tn & HTn & Hne)%O_T_spec HkC.
    assert (Hne' : co_succ T' (CoOut k c v) ≠ []) by (by eapply eff_out_keep_w).
    split.
    - eapply Htag; [exact HT'|]. apply (co_succ_tagged T' (CoOut k c v) (hd 𝟘 (co_succ T' (CoOut k c v)))), hd_elem_of, Hne'.
    - exists (hd 𝟘 (co_succ T' (CoOut k c v))). split; [apply (succ_vis T' (CoOut k c v)); by apply hd_elem_of|].
      rewrite eff_app. apply tnodes_app_elem. exists T'. split; [done|]. by apply hd_elem_of.
  Qed.

  Lemma menu_step_op n C T' k U qs :
    T' ∈ tnodes T (eff n C) → I n (OffOp k U qs) →
    ∃ T'', T' ⟶ₚ{⦅qs⦆ ! U}[{[+ k +]}] T'' ∧ T'' ∈ tnodes T (eff (n ++ [CoOp k U qs]) C).
  Proof.
    intros HT' (Tn & a & HTn & Ha & Hne). rewrite (offer_of_op a k U qs Ha) in Hne.
    assert (Hne' : co_succ T' (CoOp k U qs) ≠ []).
    { eapply eff_keep; [exact HTn|exact HT'|done|]. by intros. }
    exists (hd 𝟘 (co_succ T' (CoOp k U qs))). split; [apply (succ_vis T' (CoOp k U qs)); by apply hd_elem_of|].
    by apply (eff_menu n C (CoOp k U qs) T'), hd_elem_of.
  Qed.

  Lemma menu_step_init n C T' k q :
    T' ∈ tnodes T (eff n C) → I n (OffInit k q) →
    ∃ T'', T' ⟶ₚ{reinit q}[{[+ k +]}] T'' ∧ T'' ∈ tnodes T (eff (n ++ [CoInit k q]) C).
  Proof.
    intros HT' (Tn & a & HTn & Ha & Hne). rewrite (offer_of_init a k q Ha) in Hne.
    assert (Hne' : co_succ T' (CoInit k q) ≠ []).
    { eapply eff_keep; [exact HTn|exact HT'|done|]. by intros. }
    exists (hd 𝟘 (co_succ T' (CoInit k q))). split.
    - exact (co_succ_step _ _ _ (hd_elem_of 𝟘 _ Hne')).
    - by apply (eff_menu n C (CoInit k q) T'), hd_elem_of.
  Qed.

  Lemma menu_step_unfold n C T' k :
    T' ∈ tnodes T (eff n C) → I n (OffUnfold k) →
    ∃ T'', T' ⟶ₚ{τ}[{[+ k +]}] T'' ∧ T'' ∈ tnodes T (eff (n ++ [CoUnfold k]) C).
  Proof.
    intros HT' (Tn & a & HTn & Ha & Hne). rewrite (offer_of_unfold a k Ha) in Hne.
    assert (Hne' : co_succ T' (CoUnfold k) ≠ []).
    { eapply eff_keep; [exact HTn|exact HT'|done|]. by intros. }
    exists (hd 𝟘 (co_succ T' (CoUnfold k))). split.
    - exact (co_succ_step _ _ _ (hd_elem_of 𝟘 _ Hne')).
    - by apply (eff_menu n C (CoUnfold k) T'), hd_elem_of.
  Qed.

  Lemma menu_step_meas n C T' k M qs m :
    T' ∈ tnodes T (eff n C) → I n (OffMeas k M qs) →
    ∃ T'', T' ⟶ₚ{M ⦅qs⦆? m}[{[+ k +]}] T'' ∧ T'' ∈ tnodes T (eff (n ++ [CoMeas k M qs m]) C).
  Proof.
    intros HT' (Tn & a & HTn & Ha & Hne). destruct (offer_of_meas a k M qs Ha) as (m0 & ->).
    assert (Hne' : co_succ T' (CoMeas k M qs m) ≠ []).
    { eapply eff_keep; [exact HTn|exact HT'|by eapply co_succ_meas_out|]. by intros. }
    exists (hd 𝟘 (co_succ T' (CoMeas k M qs m))). split; [apply (succ_vis T' (CoMeas k M qs m)); by apply hd_elem_of|].
    by apply (eff_menu n C (CoMeas k M qs m) T'), hd_elem_of.
  Qed.

  (* A step of the program alone, in parallel with the observer. *)
  Lemma sched_step_parL ρ P T' s Δ :
    sched_step ρ P s Δ → sched_step ρ (P ∥ T') s ((λ Pρ, (Pρ.1 ∥ T', Pρ.2)) <$> Δ).
  Proof.
    inversion 1 as [P' Hp|U qs P' Hp|qs P' Hp|M qs Ps P0 Hp0 Hf]; subst; simpl.
    - apply ss_tau. by apply pr_parL.
    - apply ss_op. by apply pr_parL.
    - apply ss_init. by apply pr_parL.
    - rewrite fmap_zip_with'. simpl.
      replace (zip_with (λ k P', (P' ∥ T', M ⦅qs⦆[k] · ρ)) (outs_nz (meas_of M qs) ρ) Ps)
        with (zip_with (λ k R', (R', M ⦅qs⦆[k] · ρ)) (outs_nz (meas_of M qs) ρ) ((λ P', P' ∥ T') <$> Ps))
        by (rewrite zip_with_fmap_r; done).
      apply (ss_meas _ _ _ M qs _ (P0 ∥ T')); [by apply pr_parL|].
      apply Forall2_fmap_r. eapply Forall2_impl; [exact Hf|].
      intros k' P' Hp. simpl. by apply pr_parL.
  Qed.

  Lemma par_bwd ρ n P C T' it Θc :
    prog_ok P → T' ∈ tnodes T (eff n C) → dcstep ρ (n, (P, C)) it Θc →
    ∃ σ, corr σ it ∧ ∀ σ', corr σ' it →
      ∃ Δ, sched_step ρ (P ∥ T') σ' Δ ∧ Forall2 rel_par Δ Θc.
  Proof.
    intros Hok HT' Hc.
    (* the choice of an item of the observer of a given kind *)
    assert (Hkind : ∀ k t x, TG k (x) → ∀ σ', corr σ' (IOff k t) →
      (mem_kind x ∧ σ' = {[+ k +]}) ∨ (x = KIn ∧ σ' = {[+ t; k +]})).
    { intros k t x Hk σ' Hc'. inversion Hc' as [|? ? x' Hk' Hx'|? ? Hk' Ht']; subst.
      - left. rewrite (tag_kind_unique k x x' Hk Hk'). done.
      - right. rewrite (tag_kind_unique k x KIn Hk Hk'). done. }
    apply cstep_cases in Hc. inversion Hc as [? ? ? s Δ0 Hs|? ? ? k c v t P' HE HkC Hp|? ? ? k c v t P' HI Hp|? ? ? k U' qs t HI
                     |? ? ? k qs t HI|? ? ? k M qs t HI|? ? ? k t HI]; subst.
    - (* a choice of the program *)
      assert (Hs' : ∃ l P', P ⟶ₚ{l}[s] P').
      { inversion Hs as [P' Hp|U qs P' Hp|qs P' Hp|M qs Ps P0 Hp0 Hf]; subst; by eauto. }
      destruct Hs' as (l & P' & Hp).
      exists s. split; [exact (corr_prog _ _ _ _ Hok Hp)|].
      intros σ' Hc'. inversion Hc'; subst.
      eexists. split; [by apply sched_step_parL|].
      clear Hc Hc' Hp P' l. inversion Hs as [P' Hp|U qs P' Hp|qs P' Hp|M qs Ps P0 Hp0 Hf]; subst; simpl.
      + constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
      + clear Hs. revert Hf. generalize (outs_nz (meas_of M qs) ρ) as ks. intros ks Hf.
        induction Hf as [|k' P' ks Ps Hp _ IH]; simpl; [constructor|].
        constructor; [|done]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T'.
    - (* the program consumes an output *)
      destruct (out_step n C T' k c v HT' HE HkC) as (Hk & T'' & Hq & HT'').
      assert (Ht : t ∉ tgT) by (eapply prog_ok_choice; [done|exact Hp|by apply gmultiset_elem_of_singleton]).
      exists {[+ t; k +]}. split; [by apply corr_cons|].
      intros σ' Hc'. inversion Hc'; subst.
      eexists. split; [apply ss_tau; by eapply pr_syncR|].
      constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T''.
    - (* the observer inputs *)
      pose proof (menu_kind_g _ _ HI) as Hk. simpl in Hk.
      assert (Ht : t ∉ tgT) by (eapply prog_ok_choice; [done|exact Hp|by apply gmultiset_elem_of_singleton]).
      exists {[+ t; k +]}. split; [by apply corr_chan|].
      intros σ' Hc'. destruct (Hkind k t KIn Hk σ' Hc') as [[Hm _]|[_ ->]]; [by destruct Hm as [?|[?|[?|?]]]|].
      destruct (menu_step_in n C T' k c v HT' HI) as (T'' & Hq & HT'').
      eexists. split; [apply ss_tau; by eapply pr_syncL|].
      constructor; [|constructor]. split; [done|]. split; [by eapply prog_ok_step|]. by exists T''.
    - (* the observer operates on the memory *)
      pose proof (menu_kind_g _ _ HI) as Hk. simpl in Hk.
      exists ({[+ k +]}). split; [eapply corr_mem; [exact Hk|by left]|].
      intros σ' Hc'. destruct (Hkind k t KOp Hk σ' Hc') as [[_ ->]|[Hm _]]; [|done].
      destruct (menu_step_op n C T' k U' qs HT' HI) as (T'' & Hq & HT'').
      eexists. split; [apply ss_op; by apply pr_parR|].
      constructor; [|constructor]. split; [done|]. split; [done|]. by exists T''.
    - (* the observer initialises *)
      pose proof (menu_kind_g _ _ HI) as Hk. simpl in Hk.
      exists ({[+ k +]}). split; [eapply corr_mem; [exact Hk|right; right; by left]|].
      intros σ' Hc'. destruct (Hkind k t KInit Hk σ' Hc') as [[_ ->]|[Hm _]]; [|done].
      destruct (menu_step_init n C T' k qs HT' HI) as (T'' & Hq & HT'').
      eexists. split; [apply ss_init; by apply pr_parR|].
      constructor; [|constructor]. split; [done|]. split; [done|]. by exists T''.
    - (* the observer measures *)
      pose proof (menu_kind_g _ _ HI) as Hk. simpl in Hk.
      exists ({[+ k +]}). split; [eapply corr_mem; [exact Hk|right; by left]|].
      intros σ' Hc'. destruct (Hkind k t KMeas Hk σ' Hc') as [[_ ->]|[Hm _]]; [|done].
      set (f := λ k' : nat, hd 𝟘 (co_succ T' (CoMeas k M qs k'))).
      assert (Hf : ∀ k', T' ⟶ₚ{M ⦅qs⦆? k'}[{[+ k +]}] (f k')
                        ∧ f k' ∈ tnodes T (eff (n ++ [CoMeas k M qs k']) C)).
      { intros k'. destruct (menu_step_meas n C T' k M qs k' HT' HI) as (T'' & Hq & HT'').
        split.
        - apply (succ_vis T' (CoMeas k M qs k')). apply hd_elem_of. intros U.
          apply (co_succ_complete_r T' k _ T'' (proj1 (eff_obs _ _ _ HT'))) in Hq as (a & Hka & Hα & Hin).
          rewrite (co_act_meas_inv a k M qs k' Hka Hα), U in Hin. by apply elem_of_nil in Hin.
        - apply (eff_menu n C (CoMeas k M qs k') T'); [done|]. apply hd_elem_of. intros U.
          apply (co_succ_complete_r T' k _ T'' (proj1 (eff_obs _ _ _ HT'))) in Hq as (a & Hka & Hα & Hin).
          rewrite (co_act_meas_inv a k M qs k' Hka Hα), U in Hin. by apply elem_of_nil in Hin. }
      exists (zip_with (λ k' R', (R', M ⦅qs⦆[k'] · ρ)) (outs_nz (meas_of M qs) ρ) ((λ k', P ∥ f k') <$> outs_nz (meas_of M qs) ρ)).
      split.
      + destruct (menu_step_meas n C T' k M qs 0 HT' HI) as (T0 & Hq0 & _).
        apply (ss_meas _ _ _ M qs _ (P ∥ T0)); [by apply pr_parR|]. apply Forall2_fmap_r.
        generalize (outs_nz (meas_of M qs) ρ) as ks. intros ks. induction ks as [|k' ks IH]; constructor; [|done].
        simpl. apply pr_parR. apply Hf.
      + rewrite zip_with_fmap_r. generalize (outs_nz (meas_of M qs) ρ) as ks. intros ks.
        induction ks as [|k' ks IH]; simpl; [constructor|].
        constructor; [|done]. split; [done|]. split; [done|]. exists (f k'). split; [apply Hf|done].
    - (* the observer unfolds a recursion *)
      pose proof (menu_kind_g _ _ HI) as Hk. simpl in Hk.
      exists ({[+ k +]}). split; [eapply corr_mem; [exact Hk|right; right; by right]|].
      intros σ' Hc'. destruct (Hkind k t KRec Hk σ' Hc') as [[_ ->]|[Hm _]]; [|done].
      destruct (menu_step_unfold n C T' k HT' HI) as (T'' & Hq & HT'').
      eexists. split; [apply ss_tau; by apply pr_parR|].
      constructor; [|constructor]. split; [done|]. split; [done|]. by exists T''.
  Qed.

  (* ** Lifting to distributions *)

  Notation rstep := (dstep (SchedSts0 := lq_SchedSts) L).
  Notation dstep' := (dstep (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L).
  Notation rstable := (dstable (SchedSts0 := lq_SchedSts)).
  Notation dstable' := (dstable (SchedSts0 := dlts (menu T) (O_T T) (S_T T))).

  Lemma rel_comp_shape x y :
    rel_comp x y → ∃ n P C T', y.1 = (n, (P, C)) ∧ x.1 = (P, T') ∧ x.2 = y.2 ∧ prog_ok P ∧ T' ∈ tnodes T (eff n C).
  Proof.
    intros (Hρ & Hok & T' & HT' & E). destruct y as [[n [P C]] ρ']. destruct x as [[P0 T0] ρ0].
    simpl in *. injection E as -> ->. by exists n, P, C, T'.
  Qed.

  Lemma comp_fwd ρ n P C T' σ Δ :
    prog_ok P → T' ∈ tnodes T (eff n C) → conf_sched ρ (P, T') σ Δ →
    ∃ it, corr σ it ∧ ∀ it', corr σ it' →
      ∃ Θc, dcstep ρ (n, (P, C)) it' Θc ∧ Forall2 rel_comp Δ Θc.
  Proof.
    intros Hok HT' Hs. destruct (par_fwd _ _ _ _ _ _ _ Hok HT' Hs) as (it & Hc & Hall).
    exists it. split; [done|]. intros it' Hc'. destruct (Hall it' Hc') as (Θc & Hcs & HF).
    exists Θc. split; [done|]. by apply rel_dmap.
  Qed.

  Lemma comp_bwd ρ n P C T' it Θc :
    prog_ok P → T' ∈ tnodes T (eff n C) → dcstep ρ (n, (P, C)) it Θc →
    ∃ σ, corr σ it ∧ ∀ σ', corr σ' it →
      ∃ Δ, conf_sched ρ (P, T') σ' Δ ∧ Forall2 rel_comp Δ Θc.
  Proof.
    intros Hok HT' Hcs. destruct (par_bwd _ _ _ _ _ _ _ Hok HT' Hcs) as (σ & Hc & Hall).
    exists σ. split; [done|]. intros σ' Hc'. destruct (Hall σ' Hc') as (Δ & Hs & HF).
    destruct (rel_unpar _ _ HF) as (Δx & -> & HFx). by exists Δx.
  Qed.

  (* The lifted components of related components are related. *)
  Lemma rel_rest x y :
    rel_comp x y →
    Forall2 rel_comp (rest (SchedSts0 := lq_SchedSts) L x.1 x.2)
      (rest (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L y.1 y.2).
  Proof.
    intros Hxy. pose proof (rel_success x y Hxy) as Hs. destruct L; simpl.
    - constructor; [by destruct x|constructor].
    - case_decide as Hx; case_decide as Hy.
      + constructor; [by destruct x|constructor].
      + exfalso. by apply Hy, Hs.
      + exfalso. by apply Hx, Hs.
      + constructor.
  Qed.

  (* The components move together, in the two systems. *)
  Lemma comp_step_fwd x y σ it Δx :
    rel_comp x y → corr σ it → comp_step (SchedSts0 := lq_SchedSts) L x.2 x.1 σ Δx →
    ∃ Θy, comp_step (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L y.2 y.1 it Θy ∧ Forall2 rel_comp Δx Θy.
  Proof.
    intros Hxy Hc Hstep. pose proof (rel_success x y Hxy) as Hsucc. pose proof (rel_rest x y Hxy) as Hrest.
    destruct (rel_comp_shape x y Hxy) as (n & P & C & T' & Ey & Ex & Eρ & Hok & HT').
    destruct x as [cx ρx]. destruct y as [cy ρy]. simpl in *. subst cx cy ρy.
    destruct Hstep as [(Hns & Hs)|(Hst & ->)].
    - destruct (comp_fwd _ _ _ _ _ _ _ Hok HT' Hs) as (it0 & Hc0 & Hall).
      destruct (Hall it Hc) as (Θy & Hcs & HF). exists Θy. split; [|done].
      left. split; [by rewrite <- Hsucc|]. done.
    - exists (rest (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L (n, (P, C)) ρx). split.
      + right. split; [|done]. destruct Hst as [Hsu|Hno]; [left; by apply Hsucc|right].
        intros Θ' Hcs.
        destruct (comp_bwd _ _ _ _ _ _ _ Hok HT' Hcs) as (σ0 & Hc0 & Hall).
        destruct (Hall σ Hc) as (Δ' & Hs & _). by apply (Hno Δ').
      + exact Hrest.
  Qed.

  Lemma comp_step_bwd x y σ it Θy :
    rel_comp x y → corr σ it → comp_step (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L y.2 y.1 it Θy →
    ∃ Δx, comp_step (SchedSts0 := lq_SchedSts) L x.2 x.1 σ Δx ∧ Forall2 rel_comp Δx Θy.
  Proof.
    intros Hxy Hc Hstep. pose proof (rel_success x y Hxy) as Hsucc. pose proof (rel_rest x y Hxy) as Hrest.
    destruct (rel_comp_shape x y Hxy) as (n & P & C & T' & Ey & Ex & Eρ & Hok & HT').
    destruct x as [cx ρx]. destruct y as [cy ρy]. simpl in *. subst cx cy ρy.
    destruct Hstep as [(Hns & Hs)|(Hst & ->)].
    - destruct (comp_bwd _ _ _ _ _ _ _ Hok HT' Hs) as (σ0 & Hc0 & Hall).
      destruct (Hall σ Hc) as (Δx & Hsx & HF). exists Δx. split; [|done].
      left. split; [by rewrite Hsucc|]. done.
    - exists (rest (SchedSts0 := lq_SchedSts) L (P, T') ρx). split.
      + right. split; [|done]. destruct Hst as [Hsu|Hno]; [left; by apply Hsucc|right].
        intros Δ' Hsx.
        destruct (comp_fwd _ _ _ _ _ _ _ Hok HT' Hsx) as (it0 & Hc0 & Hall).
        destruct (Hall it Hc) as (Θ' & Hcs & _). by apply (Hno Θ').
      + exact Hrest.
  Qed.

  Lemma forall2_step_fwd Δ Θ σ it Δs :
    Rel Δ Θ → corr σ it → Forall2 (λ xρ Δx, comp_step (SchedSts0 := lq_SchedSts) L xρ.2 xρ.1 σ Δx) Δ Δs →
    ∃ Θs, Forall2 (λ yρ Θy, comp_step (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L yρ.2 yρ.1 it Θy) Θ Θs
      ∧ Forall2 (Forall2 rel_comp) Δs Θs.
  Proof.
    intros HR Hc HF. revert Θ HR. induction HF as [|x Δx Δ Δs Hx _ IH]; intros Θ HR.
    - inversion HR; subst. by exists [].
    - inversion HR as [|? y ? Θ' Hxy HR']; subst.
      destruct (comp_step_fwd x y σ it Δx Hxy Hc Hx) as (Θy & Hy & HFy).
      destruct (IH _ HR') as (Θs & HΘs & HFs). exists (Θy :: Θs). split; by constructor.
  Qed.

  Lemma forall2_step_bwd Δ Θ σ it Θs :
    Rel Δ Θ → corr σ it → Forall2 (λ yρ Θy, comp_step (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L yρ.2 yρ.1 it Θy) Θ Θs →
    ∃ Δs, Forall2 (λ xρ Δx, comp_step (SchedSts0 := lq_SchedSts) L xρ.2 xρ.1 σ Δx) Δ Δs
      ∧ Forall2 (Forall2 rel_comp) Δs Θs.
  Proof.
    intros HR Hc HF. revert Δ HR. induction HF as [|y Θy Θ Θs Hy _ IH]; intros Δ HR.
    - inversion HR; subst. by exists [].
    - inversion HR as [|x ? Δ' ? Hxy HR']; subst.
      destruct (comp_step_bwd x y σ it Θy Hxy Hc Hy) as (Δx & Hx & HFx).
      destruct (IH _ HR') as (Δs & HΔs & HFs). exists (Δx :: Δs). split; by constructor.
  Qed.

  Lemma dstep_fwd Δ Θ σ Δ' :
    Rel Δ Θ → rstep Δ σ Δ' → ∃ it Θ', dstep' Θ it Θ' ∧ Rel Δ' Θ'.
  Proof.
    intros HR [(c & ρ & Δc & Hin & Hns & Hs) (Δs & HF & ->)].
    destruct (Forall2_elem_of_l _ _ _ _ HR Hin) as (y & Hy & Hxy).
    destruct (rel_comp_shape (c, ρ) y Hxy) as (n & P & C & T' & Ey & Ex & Eρ & Hok & HT'). simpl in *.
    rewrite Ex in Hs. destruct (comp_fwd _ _ _ _ _ _ _ Hok HT' Hs) as (it & Hc & Hall).
    destruct (forall2_step_fwd _ _ _ _ _ HR Hc HF) as (Θs & HΘs & HFs).
    exists it, (dsum Θs). split; [|by apply Forall2_concat'].
    split; [|by exists Θs].
    destruct (Hall it Hc) as (Θc & Hcs & _). exists y.1, y.2, Θc.
    split; [by destruct y|]. split; [|by rewrite Ey, <- Eρ].
    intros Hsy. apply Hns. by apply (rel_success (c, ρ) y Hxy).
  Qed.

  Lemma dstep_bwd Δ Θ it Θ' :
    Rel Δ Θ → dstep' Θ it Θ' → ∃ σ Δ', rstep Δ σ Δ' ∧ Rel Δ' Θ'.
  Proof.
    intros HR [(y & ρ & Θc & Hin & Hns & Hcs) (Θs & HF & ->)].
    destruct (Forall2_elem_of_r _ _ _ _ HR Hin) as (x & Hx & Hxy).
    destruct (rel_comp_shape x (y, ρ) Hxy) as (n & P & C & T' & Ey & Ex & Eρ & Hok & HT'). simpl in *.
    rewrite Ey in Hcs. destruct (comp_bwd _ _ _ _ _ _ _ Hok HT' Hcs) as (σ & Hc & Hall).
    destruct (forall2_step_bwd _ _ _ _ _ HR Hc HF) as (Δs & HΔs & HFs).
    exists σ, (dsum Δs). split; [|by apply Forall2_concat'].
    split; [|by exists Δs].
    destruct (Hall σ Hc) as (Δc & Hs & _). exists x.1, x.2, Δc.
    split; [by destruct x|]. split; [|by rewrite Ex, Eρ].
    intros Hsx. apply Hns. by apply (rel_success x (y, ρ) Hxy).
  Qed.

  Lemma dstable_fwd Δ Θ : Rel Δ Θ → rstable Δ → dstable' Θ.
  Proof.
    intros HR Hst it (y & ρ & Θc & Hin & Hns & Hcs).
    destruct (Forall2_elem_of_r _ _ _ _ HR Hin) as (x & Hx & Hxy).
    destruct (rel_comp_shape x (y, ρ) Hxy) as (n & P & C & T' & Ey & Ex & Eρ & Hok & HT'). simpl in *.
    rewrite Ey in Hcs. destruct (comp_bwd _ _ _ _ _ _ _ Hok HT' Hcs) as (σ & Hc & Hall).
    destruct (Hall σ Hc) as (Δc & Hs & _).
    apply (Hst σ). exists x.1, x.2, Δc. split; [by destruct x|]. split; [|by rewrite Ex, Eρ].
    intros Hsx. apply Hns. by apply (rel_success x (y, ρ) Hxy).
  Qed.

  Lemma dstable_bwd Δ Θ : Rel Δ Θ → dstable' Θ → rstable Δ.
  Proof.
    intros HR Hst σ (c & ρ & Δc & Hin & Hns & Hs).
    destruct (Forall2_elem_of_l _ _ _ _ HR Hin) as (y & Hy & Hxy).
    destruct (rel_comp_shape (c, ρ) y Hxy) as (n & P & C & T' & Ey & Ex & Eρ & Hok & HT'). simpl in *.
    rewrite Ex in Hs. destruct (comp_fwd _ _ _ _ _ _ _ Hok HT' Hs) as (it & Hc & Hall).
    destruct (Hall it Hc) as (Θc & Hcs & _).
    apply (Hst it). exists y.1, y.2, Θc. split; [by destruct y|]. split; [|by rewrite Ey, <- Eρ].
    intros Hsy. apply Hns. by apply (rel_success (c, ρ) y Hxy).
  Qed.

  (* ** Soundness *)

  Lemma rel_init (P : proc) (ρ : St) : prog_ok P → Rel (compose (P, ρ) T) (dinit (P, ρ)).
  Proof.
    intros Hok. constructor; [|constructor]. split; [done|]. split; [done|].
    exists T. split; [|done]. unfold eff. simpl. rewrite tnodes_nil. by left.
  Qed.

  Notation dI := (dlts (menu T) (O_T T) (S_T T)).

  Lemma hstep_fwd Δ Θ Δ' :
    Rel Δ Θ → step1 (SchedSts0 := lq_SchedSts) L Δ Δ' →
    ∃ Θ1, pre (SchedSts1 := dI) L Rel (λ _, 0) Δ Θ Θ1
      ∧ ((∃ Θ', step2 (SchedSts1 := dI) L Θ1 Θ' ∧ Rel Δ' Θ') ∨ (Rel Δ' Θ1 ∧ 0 < 0)).
  Proof.
    intros HR (σ & Hs). destruct (dstep_fwd Δ Θ σ Δ' HR Hs) as (it & Θ' & Hd & HR').
    exists Θ. split; [constructor|]. left. exists Θ'. split; [by exists it|done].
  Qed.

  Lemma hstable_fwd Δ Θ :
    Rel Δ Θ → dstable (SchedSts0 := lq_SchedSts) Δ →
    ∃ Θ1, pre (SchedSts1 := dI) L Rel (λ _, 0) Δ Θ Θ1 ∧ dstable (SchedSts0 := dI) Θ1.
  Proof. intros HR Hst. exists Θ. split; [constructor|]. by eapply dstable_fwd. Qed.

  Lemma hstep_bwd Θ Δ Θ' :
    Rel Δ Θ → step1 (SchedSts0 := dI) L Θ Θ' →
    ∃ Δ1, pre (SchedSts1 := lq_SchedSts) L (λ Θ Δ, Rel Δ Θ) (λ _, 0) Θ Δ Δ1
      ∧ ((∃ Δ', step2 (SchedSts1 := lq_SchedSts) L Δ1 Δ' ∧ Rel Δ' Θ') ∨ (Rel Δ1 Θ' ∧ 0 < 0)).
  Proof.
    intros HR (it & Hs). destruct (dstep_bwd Δ Θ it Θ' HR Hs) as (σ & Δ' & Hd & HR').
    exists Δ. split; [constructor|]. left. exists Δ'. split; [by exists σ|done].
  Qed.

  Lemma hstable_bwd Θ Δ :
    Rel Δ Θ → dstable (SchedSts0 := dI) Θ →
    ∃ Δ1, pre (SchedSts1 := lq_SchedSts) L (λ Θ Δ, Rel Δ Θ) (λ _, 0) Θ Δ Δ1 ∧ dstable (SchedSts0 := lq_SchedSts) Δ1.
  Proof. intros HR Hst. exists Δ. split; [constructor|]. by eapply dstable_bwd. Qed.

  Theorem alt_pre_sound_obs (DC : dep_choice) (p q : proc * St) :
    prog_ok p.1 → prog_ok q.1 → smyth_le (SchedSts0 := dI) L (dinit p) (dinit q) →
    smyth_le (SchedSts0 := lq_SchedSts) L (compose p T) (compose q T).
  Proof.
    intros Hp Hq Halt r2 Hr2. destruct p as [P ρp]. destruct q as [Q ρq]. simpl in *.
    destruct (@run_transfer _ _ _ _ _ lq_SchedSts dI L DC Rel (λ _, 0) (λ _, 0) rel_mass hstep_fwd hstable_fwd
                _ _ r2 (rel_init Q ρq Hq) Hr2) as (r2' & Hr2' & HM1 & _).
    destruct (Halt r2' Hr2') as (r1' & Hr1' & Hle).
    destruct (@run_transfer _ _ _ _ _ dI lq_SchedSts L DC (λ Θ Δ, Rel Δ Θ) (λ _, 0) (λ _, 0)
                (λ Θ Δ HR, eq_sym (rel_mass Δ Θ HR)) hstep_bwd hstable_bwd
                _ _ r1' (rel_init P ρp Hp) Hr1') as (r1 & Hr1 & HM1' & _).
    exists r1. split; [done|].
    intros n w Hw. destruct (HM1' n) as (n1 & E1). unfold succ_mass in Hw, E1. rewrite E1 in Hw.
    destruct (Hle n1 w Hw) as (m1 & Hm1). destruct (HM1 m1) as (m & E2).
    exists m. unfold succ_mass in Hm1, E2 |- *. by rewrite <- E2.
  Qed.

  Lemma dmass_init (P : proc) (ρ : St) : dmass (compose (P, ρ) T) = dmass (dinit (P, ρ)).
  Proof. done. Qed.

  Theorem alt_as_sound_obs (DC : dep_choice) (p q : proc * St) :
    prog_ok p.1 → prog_ok q.1 →
    (pmust_as (SchedSts0 := dI) L (dinit p) → pmust_as (SchedSts0 := dI) L (dinit q)) →
    pmust_as L (compose p T) → pmust_as L (compose q T).
  Proof.
    intros Hp Hq Halt Hm. destruct p as [P ρp]. destruct q as [Q ρq]. simpl in *.
    apply (@pmust_as_transfer _ _ _ _ _ lq_SchedSts dI L DC Rel (λ _, 0) (λ _, 0) rel_mass hstep_fwd hstable_fwd
             _ _ (rel_init Q ρq Hq) (dmass_init Q ρq)).
    apply Halt.
    apply (@pmust_as_transfer _ _ _ _ _ dI lq_SchedSts L DC (λ Θ Δ, Rel Δ Θ) (λ _, 0) (λ _, 0)
             (λ Θ Δ HR, eq_sym (rel_mass Δ Θ HR)) hstep_bwd hstable_bwd
             _ _ (rel_init P ρp Hp) (eq_sym (dmass_init P ρp)) Hm).
  Qed.

  (* ** Completeness for the shape of the observer *)

  Theorem smyth_obs_complete (DC : dep_choice) (p q : proc * St) :
    prog_ok p.1 → prog_ok q.1 →
    smyth_le (SchedSts0 := lq_SchedSts) L (compose p T) (compose q T) →
    smyth_le (SchedSts0 := dI) L (dinit p) (dinit q).
  Proof.
    intros Hp Hq Hsm r2' Hr2'. destruct p as [P ρp]. destruct q as [Q ρq]. simpl in *.
    destruct (@run_transfer _ _ _ _ _ dI lq_SchedSts L DC (λ Θ Δ, Rel Δ Θ) (λ _, 0) (λ _, 0)
                (λ Θ Δ HR, eq_sym (rel_mass Δ Θ HR)) hstep_bwd hstable_bwd
                _ _ r2' (rel_init Q ρq Hq) Hr2') as (r2 & Hr2 & HM1 & _).
    destruct (Hsm r2 Hr2) as (r1 & Hr1 & Hle).
    destruct (@run_transfer _ _ _ _ _ lq_SchedSts dI L DC Rel (λ _, 0) (λ _, 0) rel_mass hstep_fwd hstable_fwd
                _ _ r1 (rel_init P ρp Hp) Hr1) as (r1' & Hr1' & HM1' & _).
    exists r1'. split; [done|].
    intros n w Hw. destruct (HM1' n) as (n1 & E1). unfold succ_mass in Hw, E1. rewrite E1 in Hw.
    destruct (Hle n1 w Hw) as (m1 & Hm1). destruct (HM1 m1) as (m & E2).
    exists m. unfold succ_mass in Hm1, E2 |- *. by rewrite <- E2.
  Qed.

  Theorem as_obs_complete (DC : dep_choice) (p q : proc * St) :
    prog_ok p.1 → prog_ok q.1 →
    (pmust_as L (compose p T) → pmust_as L (compose q T)) →
    pmust_as (SchedSts0 := dI) L (dinit p) → pmust_as (SchedSts0 := dI) L (dinit q).
  Proof.
    intros Hp Hq Hm Has. destruct p as [P ρp]. destruct q as [Q ρq]. simpl in *.
    apply (@pmust_as_transfer _ _ _ _ _ dI lq_SchedSts L DC (λ Θ Δ, Rel Δ Θ) (λ _, 0) (λ _, 0)
             (λ Θ Δ HR, eq_sym (rel_mass Δ Θ HR)) hstep_bwd hstable_bwd
             _ _ (rel_init Q ρq Hq) (eq_sym (dmass_init Q ρq))).
    apply Hm.
    apply (@pmust_as_transfer _ _ _ _ _ lq_SchedSts dI L DC Rel (λ _, 0) (λ _, 0) rel_mass hstep_fwd hstable_fwd
             _ _ (rel_init P ρp Hp) (dmass_init P ρp) Has).
  Qed.
End Sound.

Lemma observer_Htag T : observer T → ∀ n T' k x, T' ∈ tnodes T n → (k, x) ∈ tagged T' → (k, x) ∈ tagged T.
Proof.
  intros HT n T' k x HT' Hk.
  exact (elem_of_submseteq _ _ _ Hk (sublist_submseteq _ _ (tnodes_tags T (proj1 HT) n T' HT'))).
Qed.

Lemma tgT_tagged T t : t ∈ tgT (λ k x, (k, x) ∈ tagged T) → t ∈ tags T.
Proof. intros (x & Hx)%elem_of_PropSet. unfold tags. apply list_elem_of_fmap. by exists (t, x). Qed.

(* ** The theorem: [≼] is below the Smyth must for the observers *)

Definition obs_for `{QM : QuantumModel} (p q : proc * St) (T : proc) : Prop :=
  observer T ∧ ∀ t, t ∈ tags T → t ∉ otags p.1 ∧ t ∉ otags q.1.

Theorem alt_pre_sound `{QM : QuantumModel}
  (L : lifting) (DC : dep_choice) (p q : proc * St) :
  alt_pre L p q → ctx_pre_sm_on L (obs_for p q) p q.
Proof.
  intros Halt T [HT Htags].
  apply (alt_pre_sound_obs T (λ k x, (k, x) ∈ tagged T) (observer_w T HT) (observer_Htag T HT) (proj1 (proj2 HT)) L DC p q); [| |apply Halt, S_T_ext_closed].
  - intros t Ht HtT. exact (proj1 (Htags t (tgT_tagged T t HtT)) Ht).
  - intros t Ht HtT. exact (proj2 (Htags t (tgT_tagged T t HtT)) Ht).
Qed.

Theorem alt_as_sound `{QM : QuantumModel}
  (L : lifting) (DC : dep_choice) (p q : proc * St) :
  alt_as L p q → ctx_pre_as_on L (obs_for p q) p q.
Proof.
  intros Halt T [HT Htags].
  apply (alt_as_sound_obs T (λ k x, (k, x) ∈ tagged T) (observer_w T HT) (observer_Htag T HT) (proj1 (proj2 HT)) L DC p q); [| |apply Halt, S_T_ext_closed].
  - intros t Ht HtT. exact (proj1 (Htags t (tgT_tagged T t HtT)) Ht).
  - intros t Ht HtT. exact (proj2 (Htags t (tgT_tagged T t HtT)) Ht).
Qed.

(* ** The alternative preorder restricted to the shapes of observers is the
    Smyth must for these observers *)

Definition alt_pre_obs `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ T, obs_for p q T → smyth_le (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L (dinit p) (dinit q).

Lemma alt_pre_alt_pre_obs `{QM : QuantumModel} L (p q : proc * St) : alt_pre L p q → alt_pre_obs L p q.
Proof. intros Halt T _. apply Halt, S_T_ext_closed. Qed.

Theorem alt_pre_obs_iff `{QM : QuantumModel}
  (L : lifting) (DC : dep_choice) (p q : proc * St) :
  (alt_pre_obs L p q ↔ ctx_pre_sm_on L (obs_for p q) p q).
Proof.
  split.
  - intros Halt T [HT Htags].
    apply (alt_pre_sound_obs T (λ k x, (k, x) ∈ tagged T) (observer_w T HT) (observer_Htag T HT) (proj1 (proj2 HT)) L DC p q); [| |apply Halt; by split].
    + intros t Ht HtT. exact (proj1 (Htags t (tgT_tagged T t HtT)) Ht).
    + intros t Ht HtT. exact (proj2 (Htags t (tgT_tagged T t HtT)) Ht).
  - intros Hsm T [HT Htags].
    apply (smyth_obs_complete T (λ k x, (k, x) ∈ tagged T) (observer_w T HT) (observer_Htag T HT) (proj1 (proj2 HT)) L DC p q); [| |apply Hsm; by split].
    + intros t Ht HtT. exact (proj1 (Htags t (tgT_tagged T t HtT)) Ht).
    + intros t Ht HtT. exact (proj2 (Htags t (tgT_tagged T t HtT)) Ht).
Qed.

(* ** The same for the almost-sure must *)

Definition alt_as_obs `{QM : QuantumModel} (L : lifting) (p q : proc * St) : Prop :=
  ∀ T, obs_for p q T →
    pmust_as (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L (dinit p) →
    pmust_as (SchedSts0 := dlts (menu T) (O_T T) (S_T T)) L (dinit q).

Lemma alt_as_alt_as_obs `{QM : QuantumModel} L (p q : proc * St) : alt_as L p q → alt_as_obs L p q.
Proof. intros Halt T _. apply Halt, S_T_ext_closed. Qed.

Theorem alt_as_obs_iff `{QM : QuantumModel}
  (L : lifting) (DC : dep_choice) (p q : proc * St) :
  (alt_as_obs L p q ↔ ctx_pre_as_on L (obs_for p q) p q).
Proof.
  split.
  - intros Halt T [HT Htags].
    apply (alt_as_sound_obs T (λ k x, (k, x) ∈ tagged T) (observer_w T HT) (observer_Htag T HT) (proj1 (proj2 HT)) L DC p q); [| |apply Halt; by split].
    + intros t Ht HtT. exact (proj1 (Htags t (tgT_tagged T t HtT)) Ht).
    + intros t Ht HtT. exact (proj2 (Htags t (tgT_tagged T t HtT)) Ht).
  - intros Hm T [HT Htags].
    apply (as_obs_complete T (λ k x, (k, x) ∈ tagged T) (observer_w T HT) (observer_Htag T HT) (proj1 (proj2 HT)) L DC p q); [| |apply Hm; by split].
    + intros t Ht HtT. exact (proj1 (Htags t (tgT_tagged T t HtT)) Ht).
    + intros t Ht HtT. exact (proj2 (Htags t (tgT_tagged T t HtT)) Ht).
Qed.

End LqP.

(* end hide *)
