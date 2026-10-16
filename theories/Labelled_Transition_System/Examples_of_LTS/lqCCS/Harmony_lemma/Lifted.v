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
(* end hide *)
(* begin hide *)
(* * Tag schedulers are adequate for the lifted semantics of
      nondeterministic quantum programs [Feng–Xu, ASPLOS'23].

    Everything is stated over an abstract ω-cpo of super-operators [Alg],
    with measurements having finitely many outcomes.  Main result:
    [adequacy]. *)

From Stdlib Require Import List Arith Lia ChoiceFacts.
Import ListNotations.
(* ** Abstract domain of super-operators *)

Class Ord := { T : Type; le : T -> T -> Prop }.
Infix "⊑" := le (at level 70).
Definition chain `{Ord} (f : nat -> T) := forall n, f n ⊑ f (S n).

(* A measurement [m] has (at most countably many) outcomes [Out m], coded
    injectively into [nat].  [comp a b] is [a ∘ b]; [br m f] is
    [Σ_k f k ∘ ℳ_k]. *)
Class Alg `{Ord} := {
  Act : Type; Meas : Type; Out : Meas -> Type;
  code m : Out m -> nat;
  decode m : nat -> option (Out m);
  decode_code m k : decode m (code m k) = Some k;
  zero : T; one : T; comp : T -> T -> T; act : Act -> T;
  br m : (Out m -> T) -> T; sup : (nat -> T) -> T;
  le_refl a : a ⊑ a;
  le_trans a b c : a ⊑ b -> b ⊑ c -> a ⊑ c;
  le_antisym a b : a ⊑ b -> b ⊑ a -> a = b;
  zero_le a : zero ⊑ a;
  comp_assoc a b c : comp a (comp b c) = comp (comp a b) c;
  comp_1l a : comp one a = a;
  comp_1r a : comp a one = a;
  comp_0r a : comp a zero = zero;
  comp_mono a a' b b' : a ⊑ a' -> b ⊑ b' -> comp a b ⊑ comp a' b';
  br_mono m f g : (forall k, f k ⊑ g k) -> br m f ⊑ br m g;
  comp_br m f c : comp c (br m f) = br m (fun k => comp c (f k));
  sup_ub f n : chain f -> f n ⊑ sup f;
  sup_lub f x : chain f -> (forall n, f n ⊑ x) -> sup f ⊑ x;
  comp_sup_l f a : chain f -> comp (sup f) a = sup (fun n => comp (f n) a);
  comp_sup_r f a : chain f -> comp a (sup f) = sup (fun n => comp a (f n));
  br_sup m (f : nat -> Out m -> T) : (forall k, chain (fun n => f n k)) ->
    br m (fun k => sup (fun n => f n k)) = sup (fun n => br m (f n)) }.
Infix "⋅" := comp (at level 40, left associativity).

Section Lifted.
Context `{Alg}.
#[local] Hint Resolve le_refl zero_le : core.
#[local] Hint Unfold chain : core.

Lemma sup_le f g : chain f -> chain g -> (forall n, exists m, f n ⊑ g m) -> sup f ⊑ sup g.
Proof.
  intros Hf Hg Hfg. apply sup_lub; auto.
  intro n. destruct (Hfg n) as [m Hm]. eapply le_trans; eauto using sup_ub.
Qed.

Lemma sup_ext f g : chain f -> (forall n, f n = g n) -> sup f = sup g.
Proof.
  intros Hf E. assert (Hg : chain g) by (intro n; rewrite <- !E; apply Hf).
  apply le_antisym; apply sup_le; eauto; intro n; exists n; rewrite E; auto.
Qed.

Lemma sup_const a : sup (fun _ => a) = a.
Proof. apply le_antisym; [apply sup_lub | apply (sup_ub (fun _ => a) 0)]; repeat intro; auto. Qed.

Lemma sup_shift f : chain f -> sup (fun n => f (S n)) = sup f.
Proof.
  intro Hf. apply le_antisym; apply sup_le; auto; try (intro; apply Hf).
  - intro n. exists (S n). auto.
  - intro n. exists n. apply Hf.
Qed.

Lemma br_ext m f g : (forall k, f k = g k) -> br m f = br m g.
Proof. intro E. apply le_antisym; apply br_mono; intro k; rewrite E; auto. Qed.

(* ** Syntax

    [Ndet l p q] is [p □ q] with static label [l].  [Bind m f] measures [m]
    and continues with [f k] on outcome [k].  [While k m c p] carries its
    iteration counter [k] and continues on the outcomes [o] with [c o].
    [Ctx a p] is a run-time configuration: [p] running in iteration [It k]
    of the enclosing loop, or in branch [Ou j] of the enclosing measurement;
    it prefixes [a] to the tags emitted by [p].  [Done] is terminal. *)
Inductive letter := It (k : nat) | Ou (j : nat).

Inductive prog :=
| Done | Skip | Abort | Atom (a : Act) | Seq (p q : prog)
| Ndet (l : nat) (p q : prog) | Bind (m : Meas) (f : Out m -> prog)
| While (k : nat) (m : Meas) (c : Out m -> bool) (p : prog)
| Ctx (a : letter) (p : prog).

Definition tag := (nat * list letter)%type.
Definition sched := tag -> bool.

Lemma done_dec p : p = Done \/ p <> Done.
Proof. destruct p; [left | right ..]; congruence. Qed.

(* ** LTS

    [step p] describes the outgoing transitions of [p ≠ Done]: a single
    transition with Kraus operation [K], a measurement [m] (outcome [k] goes
    to [xs k]), or a nondeterministic choice tagged [t]. *)
Inductive trans :=
| Leaf (K : T) (x : prog) | Br (m : Meas) (xs : Out m -> prog) | Ch (t : tag) (x y : prog).

Definition tmap (f : prog -> prog) (g : tag -> tag) τ :=
  match τ with
  | Leaf K x => Leaf K (f x) | Br m xs => Br m (fun k => f (xs k))
  | Ch t x y => Ch (g t) (f x) (f y)
  end.

Fixpoint step p :=
  match p with
  | Done | Skip => Leaf one Done
  | Abort => Leaf zero Done
  | Atom a => Leaf (act a) Done
  | Seq p q => match p with
               | Done => Leaf one q
               | _ => tmap (fun x => Seq x q) (fun t => t) (step p) end
  | Ndet l p q => Ch (l, []) p q
  | Bind m f => Br m (fun k => Ctx (Ou (code m k)) (f k))
  | While k m c p => Br m (fun o => if c o then Seq (Ctx (It k) p) (While (S k) m c p) else Done)
  | Ctx a p => match p with
               | Done => Leaf one Done
               | _ => tmap (Ctx a) (fun t => (fst t, a :: snd t)) (step p) end
  end.

Lemma step_seq p q : p <> Done -> step (Seq p q) = tmap (fun x => Seq x q) (fun t => t) (step p).
Proof. destruct p; reflexivity || congruence. Qed.

Lemma step_ctx a p : p <> Done ->
  step (Ctx a p) = tmap (Ctx a) (fun t => (fst t, a :: snd t)) (step p).
Proof. destruct p; reflexivity || congruence. Qed.

(* [Op σ n p]: sum of the Kraus compositions of the σ-compatible terminal
    paths of length ≤ n from [p] (with multiplicity). *)
Fixpoint Op (σ : sched) n p {struct n} :=
  match p, n with
  | Done, _ => one
  | _, 0 => zero
  | _, S n =>
      match step p with
      | Leaf K x => Op σ n x ⋅ K
      | Br m xs => br m (fun k => Op σ n (xs k))
      | Ch t x y => Op σ n (if σ t then y else x)
      end
  end.

Lemma Op_S σ n p : p <> Done -> Op σ (S n) p =
  match step p with
  | Leaf K x => Op σ n x ⋅ K
  | Br m xs => br m (fun k => Op σ n (xs k))
  | Ch t x y => Op σ n (if σ t then y else x)
  end.
Proof. destruct p; reflexivity || congruence. Qed.

Lemma Op_Done σ n : Op σ n Done = one.
Proof. destruct n; reflexivity. Qed.

Lemma Op_0 σ p : p <> Done -> Op σ 0 p = zero.
Proof. destruct p; reflexivity || congruence. Qed.

Lemma Op_mono σ n p : Op σ n p ⊑ Op σ (S n) p.
Proof.
  induction n in p |- *; [destruct p; simpl; auto |].
  destruct (done_dec p) as [-> | Hp]; [rewrite !Op_Done; auto |].
  rewrite !Op_S by auto.
  destruct (step p); [apply comp_mono | apply br_mono |]; auto.
Qed.

Lemma Op_le σ n n' p : n <= n' -> Op σ n p ⊑ Op σ n' p.
Proof. induction 1; eauto using le_trans, Op_mono. Qed.

Definition E σ p := sup (fun n => Op σ n p).

Lemma chain_Op σ p : chain (fun n => Op σ n p).
Proof. intro. apply Op_mono. Qed.
#[local] Hint Resolve chain_Op : core.

Lemma E_ub σ n p : Op σ n p ⊑ E σ p.
Proof. apply (sup_ub (fun n => Op σ n p)). auto. Qed.
#[local] Hint Resolve E_ub : core.

Lemma E_Done σ : E σ Done = one.
Proof.
  unfold E. rewrite <- (sup_const one). apply sup_ext; auto. intro. apply Op_Done.
Qed.

(* One-step unfolding of the path sum. *)
Lemma E_step σ p : p <> Done -> E σ p =
  match step p with
  | Leaf K x => E σ x ⋅ K
  | Br m xs => br m (fun k => E σ (xs k))
  | Ch t x y => E σ (if σ t then y else x)
  end.
Proof.
  intro Hp. unfold E. rewrite <- sup_shift by auto.
  erewrite sup_ext; [| intro; apply Op_mono | intro; apply Op_S, Hp].
  destruct (step p).
  - symmetry. apply comp_sup_l. auto.
  - symmetry. apply (br_sup m (fun n k => Op σ n (xs k))). auto.
  - reflexivity.
Qed.

(* ** Sequence *)

Lemma Op_seq1 σ n p q : Op σ n (Seq p q) ⊑ Op σ n q ⋅ Op σ n p.
Proof.
  induction n in p |- *; [simpl; auto |].
  assert (IH : forall x, Op σ n (Seq x q) ⊑ Op σ (S n) q ⋅ Op σ n x)
    by eauto using le_trans, comp_mono, Op_mono.
  rewrite (Op_S _ _ (Seq p q)) by congruence.
  destruct (done_dec p) as [-> | Hp].
  { cbn [step]. rewrite !Op_Done. apply comp_mono; auto using Op_mono. }
  rewrite step_seq, (Op_S _ _ p) by auto.
  destruct (step p); cbn [tmap].
  - rewrite comp_assoc. apply comp_mono; auto.
  - rewrite comp_br. apply br_mono; auto.
  - destruct (σ t); auto.
Qed.

Lemma Op_seq2 σ n m p q : Op σ m q ⋅ Op σ n p ⊑ Op σ (S (n + m)) (Seq p q).
Proof.
  induction n in p |- *; rewrite (Op_S _ _ (Seq p q)) by congruence;
    (destruct (done_dec p) as [-> | Hp];
     [cbn [step]; rewrite Op_Done, !comp_1r; apply Op_le; lia |]).
  - rewrite Op_0, comp_0r by auto. auto.
  - rewrite step_seq, (Op_S _ _ p) by auto.
    destruct (step p); cbn [tmap].
    + rewrite comp_assoc. apply comp_mono; auto.
    + rewrite comp_br. apply br_mono; auto.
    + destruct (σ t); auto.
Qed.

Lemma E_seq σ p q : E σ (Seq p q) = E σ q ⋅ E σ p.
Proof.
  apply le_antisym.
  - apply sup_lub; auto. intro n.
    eapply le_trans; [apply Op_seq1 | apply comp_mono; auto].
  - change (sup (fun n => Op σ n q) ⋅ E σ p ⊑ E σ (Seq p q)).
    rewrite comp_sup_l by auto.
    apply sup_lub; [intro; apply comp_mono; auto using Op_mono |]. intro m.
    unfold E at 1. rewrite comp_sup_r by auto.
    apply sup_lub; [intro; apply comp_mono; auto using Op_mono |]. intro n.
    eapply le_trans; [apply Op_seq2 | auto].
Qed.

(* ** Contexts *)

Definition shift a (σ : sched) : sched := fun t => σ (fst t, a :: snd t).

Lemma Op_ctx1 σ a n p : Op σ n (Ctx a p) ⊑ Op (shift a σ) n p.
Proof.
  induction n in p |- *; [simpl; auto |].
  rewrite (Op_S _ _ (Ctx a p)) by congruence.
  destruct (done_dec p) as [-> | Hp]; [cbn [step]; rewrite !Op_Done, comp_1l; auto |].
  rewrite step_ctx, (Op_S _ _ p) by auto.
  destruct (step p); cbn [tmap];
    [apply comp_mono | apply br_mono | unfold shift; destruct (σ _)]; auto.
Qed.

Lemma Op_ctx2 σ a n p : Op (shift a σ) n p ⊑ Op σ (S n) (Ctx a p).
Proof.
  induction n in p |- *; rewrite (Op_S _ _ (Ctx a p)) by congruence;
    (destruct (done_dec p) as [-> | Hp]; [cbn [step]; rewrite !Op_Done, comp_1l; auto |]).
  - rewrite Op_0 by auto. auto.
  - rewrite step_ctx, (Op_S _ _ p) by auto.
    destruct (step p); cbn [tmap];
      [apply comp_mono | apply br_mono | unfold shift; destruct (σ _)]; auto.
Qed.

Lemma E_ctx σ a p : E σ (Ctx a p) = E (shift a σ) p.
Proof.
  apply le_antisym; apply sup_le; auto; intro n.
  - exists n. apply Op_ctx1.
  - exists (S n). apply Op_ctx2.
Qed.

(* ** Locality: only tags whose label occurs in [p] matter *)

Fixpoint lab p : nat -> Prop :=
  match p with
  | Seq p q => fun l => lab p l \/ lab q l
  | Ndet l0 p q => fun l => l = l0 \/ lab p l \/ lab q l
  | Bind m f => fun l => exists k, lab (f k) l
  | While _ _ _ p | Ctx _ p => lab p
  | _ => fun _ => False
  end.

Definition succ_ok p :=
  match step p with
  | Leaf _ x => forall l, lab x l -> lab p l
  | Br _ xs => forall k l, lab (xs k) l -> lab p l
  | Ch t x y => lab p (fst t) /\ (forall l, lab x l -> lab p l) /\ (forall l, lab y l -> lab p l)
  end.

Lemma step_labels p : succ_ok p.
Proof.
  unfold succ_ok. induction p.
  9: destruct (done_dec p) as [-> | Hp]; [| rewrite step_ctx by auto; destruct (step p)].
  5: destruct (done_dec p1) as [-> | Hp]; [| rewrite step_seq by auto; destruct (step p1)].
  all: cbn [step tmap lab fst] in *; intros; repeat split; intros; firstorder.
  destruct (c k0); simpl in *; tauto.
Qed.

Lemma Op_local σ σ' n p :
  (forall l w, lab p l -> σ (l, w) = σ' (l, w)) -> Op σ n p = Op σ' n p.
Proof.
  induction n in p |- *; intro Hσ;
    (destruct (done_dec p) as [-> | Hp]; [rewrite !Op_Done; auto |]).
  - rewrite !Op_0 by auto. auto.
  - rewrite !Op_S by auto. pose proof (step_labels p) as Hs. unfold succ_ok in Hs.
    destruct (step p) as [K x | m xs | [l w] x y]; simpl in Hs.
    + f_equal. apply IHn. auto.
    + apply br_ext. intro k. apply IHn. intros. apply Hσ, (Hs k); auto.
    + rewrite (Hσ l w) by tauto. destruct (σ' _); apply IHn; intuition.
Qed.

Lemma E_local σ σ' p :
  (forall l w, lab p l -> σ (l, w) = σ' (l, w)) -> E σ p = E σ' p.
Proof. intro. apply sup_ext; auto. intro. apply Op_local; auto. Qed.

(* ** Loops

    [F m c η n] is [Σ_{i ≤ n} P_exit ∘ η_{i-1} ∘ P_cont ∘ ⋯ ∘ η_0 ∘ P_cont] of
    [FX, Fig. 2], written in Horner form. *)
Fixpoint F m (c : Out m -> bool) (η : nat -> T) n :=
  match n with
  | 0 => br m (fun o => if c o then zero else one)
  | S n => br m (fun o => if c o then F m c (fun i => η (S i)) n ⋅ η 0 else one)
  end.

Lemma F_ext m c η η' n : (forall i, η i = η' i) -> F m c η n = F m c η' n.
Proof.
  induction n in η, η' |- *; intro E; simpl; [reflexivity |].
  apply br_ext. intro o. rewrite E. erewrite IHn; eauto.
Qed.

Lemma F_chain m c η : chain (F m c η).
Proof.
  intro n. induction n in η |- *; simpl; apply br_mono; intro o; destruct (c o); auto.
  apply comp_mono; auto.
Qed.
#[local] Hint Resolve F_chain : core.

Lemma E_while σ k m c p :
  E σ (While k m c p) = sup (F m c (fun i => E σ (Ctx (It (k + i)) p))).
Proof.
  set (η k i := E σ (Ctx (It (k + i)) p)).
  assert (Hη : forall k i, η k (S i) = η (S k) i) by (intros; unfold η; rewrite Nat.add_succ_r; reflexivity).
  assert (Hη0 : forall k, η k 0 = E σ (Ctx (It k) p)) by (intro; unfold η; rewrite Nat.add_0_r; auto).
  assert (U : forall k, E σ (While k m c p) =
    br m (fun o => if c o then E σ (While (S k) m c p) ⋅ E σ (Ctx (It k) p) else one)).
  { intro. rewrite E_step by congruence. cbn [step]. apply br_ext. intro o.
    destruct (c o); [apply E_seq | apply E_Done]. }
  assert (Fs : forall k j, F m c (fun i => η k (S i)) j = F m c (η (S k)) j)
    by (intros; apply F_ext, Hη).
  apply le_antisym.
  - apply sup_lub; auto. intro n. fold (η k).
    induction n in k |- *; [simpl; auto |].
    rewrite Op_S by congruence. cbn [step].
    eapply le_trans.
    { apply (br_mono m _ (fun o => if c o then sup (F m c (η (S k))) ⋅ η k 0
                                  else sup (fun _ => one))).
      intro o. destruct (c o).
      - eapply le_trans; [apply Op_seq1 |].
        rewrite Hη0. apply comp_mono; [apply IHn | auto].
      - rewrite Op_Done, sup_const. auto. }
    rewrite (br_ext m _ (fun o => sup (fun n => if c o then F m c (η (S k)) n ⋅ η k 0 else one))).
    2: { intro o. destruct (c o); [apply comp_sup_l; auto | reflexivity]. }
    rewrite (br_sup m (fun n o => if c o then F m c (η (S k)) n ⋅ η k 0 else one)).
    2: { intros o j. destruct (c o); [apply comp_mono; [apply F_chain | auto] | auto]. }
    apply sup_le; [intro; apply br_mono; intro o; destruct (c o);
                   [apply comp_mono; [apply F_chain | auto] | auto] | auto |].
    intro j. exists (S j). cbn [F]. apply br_mono. intro o. destruct (c o); [| auto].
    rewrite Fs. auto.
  - apply sup_lub; auto. intro n. fold (η k).
    induction n in k |- *; cbn [F]; rewrite U; apply br_mono; intro o; destruct (c o); auto.
    rewrite Fs, <- Hη0. apply comp_mono; auto.
Qed.

(* ** Lifted denotational semantics [FX, Fig. 2] (annotations erased) *)

Fixpoint Sem p : T -> Prop :=
  match p with
  | Done | Skip => fun x => x = one
  | Abort => fun x => x = zero
  | Atom a => fun x => x = act a
  | Seq p q => fun x => exists a b, Sem p a /\ Sem q b /\ x = b ⋅ a
  | Ndet _ p q => fun x => Sem p x \/ Sem q x
  | Bind m f => fun x => exists g, (forall k, Sem (f k) (g k)) /\ x = br m g
  | While _ m c p => fun x => exists η, (forall i, Sem p (η i)) /\ x = sup (F m c η)
  | Ctx _ p => Sem p
  end.

(* ⊇ : every tag scheduler yields an element of the lifted semantics. *)
Theorem sound σ p : Sem p (E σ p).
Proof.
  induction p in σ |- *; cbn [Sem];
    try (rewrite E_step by congruence; cbn [step]; rewrite ?E_Done, ?comp_1l, ?comp_1r; auto; fail).
  - apply E_Done.
  - rewrite E_seq. eauto 6.
  - rewrite E_step by congruence; cbn [step]. destruct (σ _); auto.
  - rewrite E_step by congruence; cbn [step].
    eexists; split; [| reflexivity]. intro k. cbv beta. rewrite E_ctx. auto.
  - rewrite E_while. eexists; split; [| reflexivity]. intro. cbv beta. rewrite E_ctx. auto.
  - rewrite E_ctx. auto.
Qed.

(* Well-labelled programs: the labels of the two sides of [;] are separated
    by a boolean predicate, and a choice label does not occur below it.
    Branches of a measurement, and iterations of a loop, may share labels. *)
Fixpoint wl p : Prop :=
  match p with
  | Seq p q => wl p /\ wl q /\
      exists d : nat -> bool, (forall l, lab p l -> d l = true) /\ (forall l, lab q l -> d l = false)
  | Ndet l p q => ~ lab p l /\ ~ lab q l /\ wl p /\ wl q
  | Bind m f => forall k, wl (f k)
  | While _ _ _ p | Ctx _ p => wl p
  | _ => True
  end.

(* ⊆ : every element of the lifted semantics is realised by a tag
    scheduler.  Needs well-labelling and countable choice (for loops and
    measurements). *)
Theorem complete (CC : FunctionalCountableChoice_on sched) p x :
  wl p -> Sem p x -> exists σ, x = E σ p.
Proof.
  induction p in x |- *; cbn [Sem wl]; intros Hwl Hx;
    try (subst; exists (fun _ => false);
         first [symmetry; apply E_Done
               | rewrite E_step by congruence; cbn [step]; rewrite E_Done, ?comp_1l, ?comp_1r; auto]; fail).
  - (* p1 ; p2 *)
    destruct Hwl as (W1 & W2 & d & D1 & D2), Hx as (a & b & Ha & Hb & ->).
    destruct (IHp1 a) as [σ0 ->], (IHp2 b) as [σ1 ->]; auto.
    exists (fun t => if d (fst t) then σ0 t else σ1 t). rewrite E_seq.
    f_equal; apply E_local; intros l w Hl; cbn [fst];
      first [rewrite D1 by auto | rewrite D2 by auto]; reflexivity.
  - (* p1 □_l p2 *)
    destruct Hwl as (N1 & N2 & W1 & W2).
    destruct Hx as [Hx | Hx];
      [ destruct (IHp1 x) as [σ0 ->]; auto;
        exists (fun t => if Nat.eqb (fst t) l then false else σ0 t)
      | destruct (IHp2 x) as [σ0 ->]; auto;
        exists (fun t => if Nat.eqb (fst t) l then true else σ0 t) ];
      rewrite (E_step _ (Ndet _ _ _)) by congruence; cbn [step fst]; rewrite Nat.eqb_refl;
      apply E_local; intros l' w Hl'; cbn [fst];
      destruct (Nat.eqb_spec l' l); subst; tauto.
  - (* measurement: branch [k] is resolved by the scheduler chosen for [code k] *)
    destruct Hx as (g & Hg & ->).
    destruct (CC (fun j σ => match decode m j with Some k => g k = E σ (f k) | None => True end))
      as [s Hs].
    { intro j. destruct (decode m j) as [k |]; [apply H1; auto | exists (fun _ => false); auto]. }
    exists (fun t => match snd t with Ou j :: w => s j (fst t, w) | _ => false end).
    rewrite (E_step _ (Bind _ _)) by congruence. cbn [step]. apply br_ext. intro k.
    specialize (Hs (code m k)). rewrite decode_code in Hs. rewrite Hs, E_ctx.
    apply E_local. reflexivity.
  - (* while: iteration k+i is resolved by the i-th chosen scheduler *)
    destruct Hx as (η & Hη & ->).
    destruct (CC (fun i σ => η i = E σ p)) as [s Hs]; [intro i; apply IHp; auto |].
    exists (fun t => match snd t with It j :: w => s (j - k) (fst t, w) | _ => false end).
    rewrite E_while. apply sup_ext; auto. intro n. apply F_ext. intro i.
    rewrite Hs, E_ctx. apply E_local. intros l w _. unfold shift. cbn [fst snd].
    replace (k + i - k) with i by lia. reflexivity.
  - (* context *)
    destruct (IHp x) as [σ ->]; auto.
    exists (fun t => σ (fst t, tl (snd t))). rewrite E_ctx. apply E_local. auto.
Qed.

(* Theorem 1 (strong form): for well-labelled [p],
    ⟦p⟧ = { Σ_{α ⊨ σ} ℰ_α : σ tag scheduler }. *)
Theorem adequacy (CC : FunctionalCountableChoice_on sched) p :
  wl p -> forall x, Sem p x <-> exists σ, x = E σ p.
Proof.
  intros Hwl x. split; [apply complete; auto |]. intros [σ ->]. apply sound.
Qed.

End Lifted.
(* end hide *)
