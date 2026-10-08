(** * Path sums (Lemma 4.7)

    For finite branching, [Op σ n p] is the sum, over the σ-compatible
    terminal paths of length ≤ n from [p], of the composition of their Kraus
    decorations.  The enumeration [enum σ n p] lists exactly these paths,
    each once ([enum_spec], [enum_nodup]). *)
From Stdlib Require Import List Arith Lia FinFun ChoiceFacts.
From TestingTheory Require Import Lifted.
Import ListNotations.

(** Finite branching: outcomes are enumerated, [+] exists, and [br] is the
    sum of its branches precomposed with the Kraus maps [ℳ_k]. *)
Class FinAlg `{Alg} := {
  add : T -> T -> T;
  kraus m : Out m -> T;
  outs m : list (Out m);
  outs_nodup m : NoDup (outs m);
  outs_all m k : In k (outs m);
  add_0l a : add zero a = a;
  add_0r a : add a zero = a;
  add_assoc a b c : add a (add b c) = add (add a b) c;
  comp_addl a b c : add a b ⋅ c = add (a ⋅ c) (b ⋅ c);
  comp_0l c : zero ⋅ c = zero;
  br_sum m f : br m f = fold_right add zero (map (fun k => f k ⋅ kraus m k) (outs m)) }.

Section Paths.
Context `{FinAlg}.

Definition sum := fold_right add zero.

Lemma sum_app l1 l2 : sum (l1 ++ l2) = add (sum l1) (sum l2).
Proof. induction l1; simpl; [now rewrite add_0l | now rewrite IHl1, add_assoc]. Qed.

Lemma sum_comp l c : sum l ⋅ c = sum (map (fun a => a ⋅ c) l).
Proof. induction l; simpl; [apply comp_0l | now rewrite comp_addl, IHl]. Qed.

(** ** Labelled transitions and paths *)

Inductive lbl := Eps | Mk (m : Meas) (j : nat) | Chs (t : tag) (b : bool).

(** [ts p λ K x]: a transition [p --λ|K--> x]. *)
Definition ts p λ K x : Prop :=
  p <> Done /\
  match step p with
  | Leaf K' x' => λ = Eps /\ K = K' /\ x = x'
  | Br m xs => exists k, λ = Mk m (code m k) /\ K = kraus m k /\ x = xs k
  | Ch t x0 x1 => exists b, λ = Chs t b /\ K = one /\ x = if b then x1 else x0
  end.

(** Terminal paths, as lists of (label, Kraus decoration). *)
Inductive tpath : prog -> list (lbl * T) -> Prop :=
| tp_done : tpath Done []
| tp_cons p λ K x α : ts p λ K x -> tpath x α -> tpath p ((λ, K) :: α).

Definition compat (σ : sched) (α : list (lbl * T)) :=
  Forall (fun e => match fst e with Chs t b => b = σ t | _ => True end) α.

(** [kr α] = K_n ∘ ⋯ ∘ K_1. *)
Fixpoint kr (α : list (lbl * T)) :=
  match α with [] => one | (_, K) :: α => kr α ⋅ K end.

(** ** Enumeration of compatible terminal paths of length ≤ n *)

Fixpoint enum (σ : sched) n p {struct n} : list (list (lbl * T)) :=
  match p, n with
  | Done, _ => [[]]
  | _, 0 => []
  | _, S n =>
      match step p with
      | Leaf K x => map (cons (Eps, K)) (enum σ n x)
      | Br m xs => flat_map (fun k => map (cons (Mk m (code m k), kraus m k)) (enum σ n (xs k)))
                            (outs m)
      | Ch t x y => map (cons (Chs t (σ t), one)) (enum σ n (if σ t then y else x))
      end
  end.

Lemma enum_Done σ n : enum σ n Done = [[]].
Proof. destruct n; reflexivity. Qed.

Lemma enum_0 σ p : p <> Done -> enum σ 0 p = [].
Proof. destruct p; reflexivity || congruence. Qed.

Lemma enum_S σ n p : p <> Done -> enum σ (S n) p =
  match step p with
  | Leaf K x => map (cons (Eps, K)) (enum σ n x)
  | Br m xs => flat_map (fun k => map (cons (Mk m (code m k), kraus m k)) (enum σ n (xs k)))
                        (outs m)
  | Ch t x y => map (cons (Chs t (σ t), one)) (enum σ n (if σ t then y else x))
  end.
Proof. destruct p; reflexivity || congruence. Qed.

Lemma sum_flat_map {A} (g : A -> list (list (lbl * T))) l :
  sum (map kr (flat_map g l)) = sum (map (fun a => sum (map kr (g a))) l).
Proof. induction l; simpl; [reflexivity | now rewrite map_app, sum_app, IHl]. Qed.

Lemma sum_cons λ K l : sum (map kr (map (cons (λ, K)) l)) = sum (map kr l) ⋅ K.
Proof. rewrite sum_comp, !map_map. reflexivity. Qed.

(** Lemma 4.7. *)
Theorem path_sum σ n p : Op σ n p = sum (map kr (enum σ n p)).
Proof.
  induction n in p |- *; destruct (done_dec p) as [-> | Hp].
  1,3: rewrite Op_Done, enum_Done; simpl; now rewrite add_0r.
  - now rewrite Op_0, enum_0.
  - rewrite Op_S, enum_S by auto. destruct (step p) as [K x | m xs | t x y].
    + now rewrite sum_cons, IHn.
    + rewrite br_sum, sum_flat_map. change (fold_right add zero) with sum.
      f_equal. apply map_ext. intro k. now rewrite sum_cons, IHn.
    + now rewrite sum_cons, comp_1r, IHn.
Qed.

(** The enumeration lists exactly the compatible terminal paths of length ≤ n. *)
Theorem enum_spec σ n p α :
  In α (enum σ n p) <-> tpath p α /\ compat σ α /\ length α <= n.
Proof.
  induction n in p, α |- *; destruct (done_dec p) as [-> | Hp].
  1,3: rewrite enum_Done; split; [intros [<- | []]; repeat constructor; simpl; lia |].
  1,2: intros [Hα _]; inversion Hα as [| ? ? ? ? ? Ht]; [now left | destruct Ht; congruence].
  - rewrite enum_0 by auto. split; [intros [] |].
    intros (Hα & _ & Hl). inversion Hα; subst; simpl in Hl; [congruence | lia].
  - rewrite enum_S by auto. split.
    + intro Hin. destruct (step p) as [K x | m xs | t x y] eqn:Hs.
      * apply in_map_iff in Hin as (α' & <- & Hin). apply IHn in Hin as (P & C & L).
        repeat split; [| constructor; [exact I | auto] | simpl; lia].
        econstructor; [| eauto]. split; [auto | rewrite Hs; auto].
      * apply in_flat_map in Hin as (k & _ & Hin). apply in_map_iff in Hin as (α' & <- & Hin).
        apply IHn in Hin as (P & C & L).
        repeat split; [| constructor; [exact I | auto] | simpl; lia].
        econstructor; [| eauto]. split; [auto | rewrite Hs; eauto].
      * apply in_map_iff in Hin as (α' & <- & Hin). apply IHn in Hin as (P & C & L).
        repeat split; [| constructor; [reflexivity | auto] | simpl; lia].
        econstructor; [| eauto]. split; [auto | rewrite Hs; eauto].
    + intros (Hα & C & L). inversion Hα as [| ? λ K x α' [_ Ht] P]; subst; [congruence |].
      inversion C as [| ? ? Cb C']; subst. simpl in L.
      assert (IH : In α' (enum σ n x)) by (apply IHn; repeat split; auto; lia).
      destruct (step p) as [K' x' | m xs | t x0 x1].
      * destruct Ht as (-> & -> & ->). apply in_map. auto.
      * destruct Ht as (k & -> & -> & ->). apply in_flat_map. exists k.
        split; [apply outs_all | apply in_map; auto].
      * destruct Ht as (b & -> & -> & ->). simpl in Cb. subst b. apply in_map. auto.
Qed.

(** Each path is listed once: the sum counts paths with multiplicity. *)
Lemma code_inj m k k' : code m k = code m k' -> k = k'.
Proof. intro E. pose proof (decode_code m k) as D. rewrite E, decode_code in D. congruence. Qed.

Lemma NoDup_app' {A} (l1 l2 : list A) : NoDup l1 -> NoDup l2 ->
  (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a l1 IH]; simpl; auto. intros N1 N2 D. inversion N1; subst.
  constructor; [rewrite in_app_iff; firstorder | apply IH; firstorder].
Qed.

Lemma NoDup_cons_map {A} (a : A) l : NoDup l -> NoDup (map (cons a) l).
Proof. intro. apply Injective_map_NoDup; auto. intros x y E. now injection E. Qed.

Theorem enum_nodup σ n p : NoDup (enum σ n p).
Proof.
  induction n in p |- *; destruct (done_dec p) as [-> | Hp].
  1,3: rewrite enum_Done; repeat constructor; auto.
  - rewrite enum_0 by auto. constructor.
  - rewrite enum_S by auto. destruct (step p) as [K x | m xs | t x y]; try now apply NoDup_cons_map.
    pose proof (outs_nodup m) as N. induction N as [| k ks Nk N IHN]; simpl; [constructor |].
    apply NoDup_app'; [now apply NoDup_cons_map | auto |].
    intros α A1 A2. apply in_map_iff in A1 as (α1 & <- & _).
    apply in_flat_map in A2 as (k' & Hk' & A2). apply in_map_iff in A2 as (α2 & E & _).
    injection E as Ec _. apply code_inj in Ec. subst. contradiction.
Qed.

(** ** Distinct labels imply well-labelling

    With finitely many outcomes the labels of a program form a list; if no
    label is repeated (the hypothesis of Theorem 4.10 in the paper), the
    program is well-labelled in the sense of [wl]. *)

Fixpoint labels p : list nat :=
  match p with
  | Seq p q => labels p ++ labels q
  | Ndet l p q => l :: labels p ++ labels q
  | Bind m f => flat_map (fun k => labels (f k)) (outs m)
  | While _ _ _ p | Ctx _ p => labels p
  | _ => []
  end.

Lemma lab_labels p l : lab p l <-> In l (labels p).
Proof.
  induction p; simpl; rewrite ?in_app_iff; try tauto.
  - rewrite IHp1, IHp2. split; intros [-> | Hl]; auto.
  - rewrite in_flat_map. split.
    + intros [k Hk]. exists k. split; [apply outs_all | apply H2, Hk].
    + intros (k & _ & Hk). exists k. apply H2, Hk.
Qed.

Lemma NoDup_disj (l1 l2 : list nat) a : NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
  induction l1 as [| b l1 IH]; simpl; [tauto |]. inversion 1 as [| ? ? Hb Hnd]; subst.
  intros [-> | Ha] Hc; [rewrite in_app_iff in Hb; tauto | eapply IH; eauto].
Qed.

Lemma NoDup_flat_map_in {A} (g : A -> list nat) l k :
  NoDup (flat_map g l) -> In k l -> NoDup (g k).
Proof.
  induction l as [| a l IH]; simpl; [tauto |]. intros N [-> | Hk].
  - eapply NoDup_app_remove_r; eauto.
  - apply IH; auto. eapply NoDup_app_remove_l; eauto.
Qed.

Theorem nodup_wl p : NoDup (labels p) -> wl p.
Proof.
  induction p; simpl; intro N; auto.
  - repeat split; [apply IHp1; eapply NoDup_app_remove_r; eauto
                  | apply IHp2; eapply NoDup_app_remove_l; eauto |].
    exists (fun l => if in_dec Nat.eq_dec l (labels p1) then true else false).
    split; intros l Hl; apply lab_labels in Hl; destruct in_dec; auto.
    exfalso. eapply NoDup_disj; eauto.
  - inversion N as [| ? ? Hl N']; subst. rewrite in_app_iff in Hl.
    rewrite !lab_labels. repeat split; try tauto;
      [apply IHp1; eapply NoDup_app_remove_r | apply IHp2; eapply NoDup_app_remove_l]; eauto.
  - intro k. apply H2, (NoDup_flat_map_in (fun k => labels (f k)) (outs m)); [exact N | apply outs_all].
Qed.

(** Theorem 4.10 with the hypothesis of the paper. *)
Corollary adequacy_nodup (CC : ChoiceFacts.FunctionalCountableChoice_on sched) p :
  NoDup (labels p) -> forall x, Sem p x <-> exists σ, x = E σ p.
Proof. intro N. apply adequacy; auto. apply nodup_wl, N. Qed.

End Paths.
