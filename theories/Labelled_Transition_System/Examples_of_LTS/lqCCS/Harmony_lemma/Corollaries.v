(** * State-level corollaries: Corollary 4.12, Corollary 5.6 and pruning

    - [cor_states]: ⟦p⟧(ρ) is the set of limits of the sums of final states
      over σ-compatible terminal paths of the configuration LTS.
    - [cor_par]: the same for the paths of (p ∥ ρ)\L.
    - [pruning]: ⟦p⟧ = { ⟦prune_σ(p) ∥ −⟧ : σ }, where the program LTS is
      pruned to the choices allowed by σ before composition with the memory. *)
From Stdlib Require Import List ChoiceFacts.
From TestingTheory Require Import Lifted Paths States Harmony.
Import ListNotations.

Section Corollaries.
Context `{StAlg}.

(** ** Configuration LTS: ⟨p, ρ⟩ --α--> ⟨Done, ρ'⟩ *)

Inductive cpath : prog -> St -> list (lbl * T) -> St -> Prop :=
| cp_done ρ : cpath Done ρ [] ρ
| cp_cons p ρ λ K x α ρ' : ts p λ K x -> cpath x (app K ρ) α ρ' -> cpath p ρ ((λ, K) :: α) ρ'.

(** The final state of a path is ℰ_α(ρ). *)
Lemma cpath_iff p ρ α ρ' : cpath p ρ α ρ' <-> tpath p α /\ ρ' = app (kr α) ρ.
Proof.
  split.
  - induction 1 as [ρ | p ρ λ K x α ρ' Ht Hc [P ->]]; simpl.
    + split; [constructor | now rewrite app_one].
    + split; [econstructor; eauto | now rewrite app_comp].
  - intros [P ->]. induction P as [| p λ K x α Ht P IH] in ρ |- *; simpl.
    + rewrite app_one. constructor.
    + rewrite app_comp. econstructor; eauto.
Qed.

(** Depth-n value: sum of the final states of the σ-compatible terminal paths
    of length ≤ n (each listed once by [enum_spec], [enum_nodup]). *)
Definition CV σ n p ρ := ssum (map (fun α => app (kr α) ρ) (enum σ n p)).

Lemma CV_spec σ n p ρ α ρ' :
  (In α (enum σ n p) /\ ρ' = app (kr α) ρ) <->
  (cpath p ρ α ρ' /\ compat σ α /\ length α <= n).
Proof. rewrite enum_spec, cpath_iff. tauto. Qed.

Lemma app_E σ p ρ : app (E σ p) ρ = ssup (fun n => CV σ n p ρ).
Proof.
  apply app_sup; [intro; apply Op_mono |].
  intro n. unfold CV. rewrite path_sum, app_ssum, map_map. reflexivity.
Qed.

(** Corollary 4.12. *)
Theorem cor_states (CC : FunctionalCountableChoice_on sched) p ρ s :
  NoDup (labels p) ->
  (exists x, Sem p x /\ s = app x ρ) <-> exists σ, s = ssup (fun n => CV σ n p ρ).
Proof.
  intro N. split.
  - intros (x & Hx & ->). destruct (proj1 (adequacy_nodup CC p N x) Hx) as [σ ->].
    exists σ. apply app_E.
  - intros [σ ->]. exists (E σ p). split; [apply sound | symmetry; apply app_E].
Qed.

(** ** Paths of (p ∥ ρ)\L *)

Lemma ts_det p λ K K' x x' : ts p λ K x -> ts p λ K' x' -> K = K' /\ x = x'.
Proof.
  intros [Hp T1] [_ T2]. destruct (step p) as [K0 x0 | m xs | t y0 y1].
  - destruct T1 as (-> & -> & ->), T2 as (_ & -> & ->). auto.
  - destruct T1 as (k & -> & -> & ->), T2 as (k' & E & -> & ->).
    injection E as E. apply code_inj in E. subst. auto.
  - destruct T1 as (b & -> & -> & ->), T2 as (b' & E & -> & ->).
    injection E as <-. auto.
Qed.

(** Different terminal paths give different composed paths. *)
Lemma hats_inj p α α' : tpath p α -> tpath p α' -> hats α = hats α' -> α = α'.
Proof.
  intro P. induction P as [| p λ K x α Ht P IH] in α' |- *; intros P' E.
  - destruct α'; [reflexivity | discriminate].
  - destruct α' as [| [λ' K'] α']; [discriminate |]. simpl in E. injection E as E1 E2.
    assert (λ' = λ) as -> by (rewrite <- (erase_hat λ' K'), <- E1; apply erase_hat).
    inversion P' as [| ? ? ? x' ? Ht' P'']; subst.
    destruct (ts_det _ _ _ _ _ _ Ht Ht') as [<- <-]. f_equal. apply IH; auto.
Qed.

(** Composed paths of length ≤ n, with their final memories. *)
Definition penum σ n p ρ := map (fun α => (hats α, app (kr α) ρ)) (enum σ n p).

Theorem penum_spec σ n p ρ β ρ' :
  In (β, ρ') (penum σ n p ρ) <-> ppath p ρ β ρ' /\ ccompat σ β /\ length β <= n.
Proof.
  unfold penum. rewrite in_map_iff. split.
  - intros (α & [= <- <-] & Hin). apply enum_spec in Hin as (P & C & L).
    repeat split; [apply harmony_paths, P | apply compat_hats, C | unfold hats; now rewrite length_map].
  - intros (Pp & C & L). apply harmony_paths_inv in Pp as (α & P & <- & ->).
    exists α. split; [reflexivity |]. apply enum_spec. repeat split; auto.
    + apply compat_hats, C.
    + unfold hats in L. now rewrite length_map in L.
Qed.

Lemma NoDup_map_on {A B} (f : A -> B) l :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hf N. induction N as [| a l Ha N IH]; simpl; constructor.
  - rewrite in_map_iff. intros (b & E & Hb). apply Ha.
    rewrite (Hf b a) in Hb; simpl; auto.
  - apply IH. intros. apply Hf; simpl; auto.
Qed.

Theorem penum_nodup σ n p ρ : NoDup (penum σ n p ρ).
Proof.
  apply NoDup_map_on; [| apply enum_nodup].
  intros α α' Hα Hα' E. injection E as E _.
  apply enum_spec in Hα as [P _], Hα' as [P' _]. apply (hats_inj p); auto.
Qed.

Definition PV σ n p ρ := ssum (map snd (penum σ n p ρ)).

Lemma PV_CV σ n p ρ : PV σ n p ρ = CV σ n p ρ.
Proof. unfold PV, CV, penum. now rewrite map_map. Qed.

Lemma app_E_par σ p ρ : app (E σ p) ρ = ssup (fun n => PV σ n p ρ).
Proof.
  apply app_sup; [intro; apply Op_mono |].
  intro n. rewrite PV_CV. unfold CV. rewrite path_sum, app_ssum, map_map. reflexivity.
Qed.

(** Corollary 5.6. *)
Theorem cor_par (CC : FunctionalCountableChoice_on sched) p ρ s :
  NoDup (labels p) ->
  (exists x, Sem p x /\ s = app x ρ) <-> exists σ, s = ssup (fun n => PV σ n p ρ).
Proof.
  intro N. split.
  - intros (x & Hx & ->). destruct (proj1 (adequacy_nodup CC p N x) Hx) as [σ ->].
    exists σ. apply app_E_par.
  - intros [σ ->]. exists (E σ p). split; [apply sound | symmetry; apply app_E_par].
Qed.

(** ** Pruning: resolve the choices on the program LTS, then compose

    [ppstep σ] is the program LTS of [Harmony] with only the choice
    transitions [(t, σ t)] kept; [cpar P] composes a program LTS [P] with the
    memory, as [par] does for the unpruned one. *)
Definition ppstep (σ : sched) p a x :=
  pstep p a x /\ match a with Pick t b => b = σ t | _ => True end.

Inductive cpar (P : prog -> plbl -> prog -> Prop) : prog -> St -> clbl -> prog -> St -> Prop :=
| cpar_op p x ρ ρ' K : P p (Emit K) x -> mstep ρ (Apply K) ρ' -> cpar P p ρ (TauOp K) x ρ'
| cpar_meas p x ρ ρ' m j :
    P p (Recv m j) x -> mstep ρ (Send m j) ρ' -> cpar P p ρ (TauMeas m j) x ρ'
| cpar_ch p x ρ t b : P p (Pick t b) x -> cpar P p ρ (Choice t b) x ρ.

Inductive cppath (P : prog -> plbl -> prog -> Prop) : prog -> St -> list clbl -> St -> Prop :=
| cpp_done ρ : cppath P Done ρ [] ρ
| cpp_cons p ρ a x ρ1 β ρ' : cpar P p ρ a x ρ1 -> cppath P x ρ1 β ρ' -> cppath P p ρ (a :: β) ρ'.

Lemma cpar_prune σ p ρ a x ρ' :
  cpar (ppstep σ) p ρ a x ρ' <->
  par p ρ a x ρ' /\ match a with Choice t b => b = σ t | _ => True end.
Proof.
  split.
  - intro C. destruct C as [? ? ? ? ? [S _] M | ? ? ? ? ? ? [S _] M | ? ? ? ? ? [S B]].
    + split; [econstructor; eauto | exact I].
    + split; [econstructor; eauto | exact I].
    + split; [econstructor; eauto | exact B].
  - intros [C B]. destruct C as [? ? ? ? ? S M | ? ? ? ? ? ? S M | ? ? ? ? ? S].
    + econstructor; [split; [exact S | exact I] | exact M].
    + econstructor; [split; [exact S | exact I] | exact M].
    + econstructor. split; [exact S | exact B].
Qed.

(** The paths of the pruned composition are the σ-compatible composed paths. *)
Lemma cppath_prune σ p ρ β ρ' :
  cppath (ppstep σ) p ρ β ρ' <-> ppath p ρ β ρ' /\ ccompat σ β.
Proof.
  split.
  - induction 1 as [ρ | p ρ a x ρ1 β ρ' C _ [Pp Cc]].
    + split; constructor.
    + apply cpar_prune in C as [C B]. split; [econstructor; eauto | constructor; auto].
  - intros [Pp Cc]. induction Pp as [ρ | p ρ a x ρ1 β ρ' C Pp IH]; [constructor |].
    inversion Cc as [| ? ? B Cc']; subst.
    econstructor; [apply cpar_prune; split; eauto | apply IH; auto].
Qed.

Theorem penum_prune σ n p ρ β ρ' :
  In (β, ρ') (penum σ n p ρ) <-> cppath (ppstep σ) p ρ β ρ' /\ length β <= n.
Proof. rewrite penum_spec, cppath_prune. tauto. Qed.

(** ⟦prune_σ(p) ∥ −⟧: the state map computed by the pruned composition. *)
Definition pruned σ p (ρ : St) := ssup (fun n => PV σ n p ρ).

(** ⟦p⟧ = { ⟦prune_σ(p) ∥ −⟧ : σ }. *)
Theorem pruning (CC : FunctionalCountableChoice_on sched) p x :
  NoDup (labels p) -> Sem p x <-> exists σ, forall ρ, app x ρ = pruned σ p ρ.
Proof.
  intro N. split.
  - intro Hx. destruct (proj1 (adequacy_nodup CC p N x) Hx) as [σ ->].
    exists σ. intro ρ. apply app_E_par.
  - intros [σ Hσ]. replace x with (E σ p); [apply sound |].
    apply app_ext. intro ρ. rewrite Hσ. apply app_E_par.
Qed.

End Corollaries.
