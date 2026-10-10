(* begin hide *)
(* * Harmony lemma (Lemma 5.1): program ∥ memory

    The configuration LTS ⟨p, ρ⟩ --λ--> ⟨x, K(ρ)⟩ is in bijection with the
    restricted parallel composition (p ∥ ρ)\L of a classical program LTS,
    which emits operations and receives outcomes, and a memory LTS. *)
From Stdlib Require Import List.
From TestingTheory Require Import Lifted Paths States.
Import ListNotations.

Section Harmony.
Context `{StAlg}.

(* Configuration LTS. *)
Definition cstep (p : prog) (ρ : St) λ x ρ' := exists K, ts p λ K x /\ ρ' = app K ρ.

(* Program LTS: purely classical. *)
Inductive plbl := Emit (K : T) | Recv (m : Meas) (j : nat) | Pick (t : tag) (b : bool).

Definition pstep p a x : Prop :=
  p <> Done /\
  match step p with
  | Leaf K x' => a = Emit K /\ x = x'
  | Br m xs => exists k, a = Recv m (code m k) /\ x = xs k
  | Ch t x0 x1 => exists b, a = Pick t b /\ x = if b then x1 else x0
  end.

(* Memory LTS. *)
Inductive mlbl := Apply (K : T) | Send (m : Meas) (j : nat).

Inductive mstep : St -> mlbl -> St -> Prop :=
| m_apply ρ K : mstep ρ (Apply K) (app K ρ)
| m_send ρ m k : mstep ρ (Send m (code m k)) (app (kraus m k) ρ).

(* Restricted composition: operations and outcomes must synchronise. *)
Inductive clbl := TauOp (K : T) | TauMeas (m : Meas) (j : nat) | Choice (t : tag) (b : bool).

Inductive par : prog -> St -> clbl -> prog -> St -> Prop :=
| par_op p x ρ ρ' K : pstep p (Emit K) x -> mstep ρ (Apply K) ρ' -> par p ρ (TauOp K) x ρ'
| par_meas p x ρ ρ' m j :
    pstep p (Recv m j) x -> mstep ρ (Send m j) ρ' -> par p ρ (TauMeas m j) x ρ'
| par_ch p x ρ t b : pstep p (Pick t b) x -> par p ρ (Choice t b) x ρ.

Definition hat (λ : lbl) (K : T) : clbl :=
  match λ with Eps => TauOp K | Mk m j => TauMeas m j | Chs t b => Choice t b end.

Definition erase (a : clbl) : lbl :=
  match a with TauOp _ => Eps | TauMeas m j => Mk m j | Choice t b => Chs t b end.

Lemma erase_hat λ K : erase (hat λ K) = λ.
Proof. now destruct λ. Qed.

(* Every configuration transition is a transition of the composition ... *)
Theorem harmony p ρ λ K x : ts p λ K x -> par p ρ (hat λ K) x (app K ρ).
Proof.
  intros [Hp Ht]. destruct (step p) as [K' x' | m xs | t x0 x1] eqn:Hs.
  - destruct Ht as (-> & -> & ->). constructor; [split; [auto | rewrite Hs; auto] | constructor].
  - destruct Ht as (k & -> & -> & ->). constructor; [split; [auto | rewrite Hs; eauto] | constructor].
  - destruct Ht as (b & -> & -> & ->). rewrite app_one.
    constructor. split; [auto | rewrite Hs; eauto].
Qed.

(* ... and every transition of the composition arises this way, from a
    unique configuration transition (the label and decoration are
    recovered by [erase] and [hat]). *)
Theorem harmony_inv p ρ a x ρ' :
  par p ρ a x ρ' -> exists K, ts p (erase a) K x /\ ρ' = app K ρ /\ hat (erase a) K = a.
Proof.
  intro Hpar. destruct Hpar as [p x ρ ρ' K [Hp Ht] Hm | p x ρ ρ' m j [Hp Ht] Hm | p x ρ t b [Hp Ht]];
    destruct (step p) as [K' x' | m' xs | t' x0 x1] eqn:Hs; cbn [erase hat].
  all: try (destruct Ht as [? _]; discriminate); try (destruct Ht as (? & ? & _); discriminate).
  - destruct Ht as [[= ->] ->]. inversion Hm; subst.
    exists K'. split; [split; [auto | rewrite Hs; auto] | auto].
  - destruct Ht as (k & [= -> ->] & ->). inversion Hm; subst.
    match goal with E : code _ _ = code _ _ |- _ => apply code_inj in E; subst end.
    exists (kraus m' k). split; [split; [auto | rewrite Hs; eauto] | auto].
  - destruct Ht as (b' & [= -> ->] & ->). exists one.
    split; [split; [auto | rewrite Hs; eauto] | rewrite app_one; auto].
Qed.

(* ** Paths *)

Inductive ppath : prog -> St -> list clbl -> St -> Prop :=
| pp_done ρ : ppath Done ρ [] ρ
| pp_cons p ρ a x ρ1 β ρ' : par p ρ a x ρ1 -> ppath x ρ1 β ρ' -> ppath p ρ (a :: β) ρ'.

Definition hats (α : list (lbl * T)) := map (fun e => hat (fst e) (snd e)) α.

(* Terminal paths correspond, with the same final memory [ℰ_α(ρ)]. *)
Theorem harmony_paths p ρ α : tpath p α -> ppath p ρ (hats α) (app (kr α) ρ).
Proof.
  intro Hα. induction Hα as [| p λ K x α Ht Hα IH] in ρ |- *; simpl.
  - rewrite app_one. constructor.
  - rewrite app_comp. econstructor; [apply harmony, Ht | apply IH].
Qed.

Theorem harmony_paths_inv p ρ β ρ' :
  ppath p ρ β ρ' -> exists α, tpath p α /\ hats α = β /\ ρ' = app (kr α) ρ.
Proof.
  intro Hβ. induction Hβ as [ρ | p ρ a x ρ1 β ρ' Hpar Hβ IH].
  - exists []. repeat split; [constructor | simpl; now rewrite app_one].
  - destruct IH as (α & Hα & <- & ->). apply harmony_inv in Hpar as (K & Ht & -> & Ha).
    exists ((erase a, K) :: α). repeat split.
    + econstructor; eauto.
    + simpl. now rewrite Ha.
    + simpl. now rewrite app_comp.
Qed.

(* Scheduler compatibility only reads the [Choice] labels of the program
    side: resolving choices before or after composition with the memory is
    the same (pruning, §5). *)
Definition ccompat (σ : sched) (β : list clbl) :=
  Forall (fun a => match a with Choice t b => b = σ t | _ => True end) β.

Lemma compat_hats σ α : compat σ α <-> ccompat σ (hats α).
Proof.
  induction α as [| [λ K] α IH]; simpl; [split; constructor |].
  split; intro C; inversion C; subst; constructor; try apply IH; auto; destruct λ; auto.
Qed.

End Harmony.
(* end hide *)
