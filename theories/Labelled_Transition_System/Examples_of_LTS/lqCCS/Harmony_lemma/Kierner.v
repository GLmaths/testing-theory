(* begin hide *)
(* * Tag schedulers are history-dependent schedulers (§3, inclusion ⊆)

    Every element of ⟦p⟧(ρ) is the value of the MDP of [Kierner 2025] under
    some history-dependent scheduler.  The scheduler built here reads only
    the sequence of quantum states visited so far, so it is a scheduler of
    that MDP a fortiori.  It replays the program: at a measurement it
    recovers the outcome from the next state, which requires outcomes to be
    distinguishable ([distinct_outcomes], true for projective
    measurements); at a choice it applies the tag scheduler to the tag it
    has reconstructed.

    States are kept unnormalised: along a path, (probability) × (normalised
    final state) is the unnormalised final state, and the unnormalised
    states are a function of the normalised history. *)
From Stdlib Require Import List ChoiceFacts.
From TestingTheory Require Import Lifted Paths States.
Import ListNotations.

(* Measurement outcomes can be recovered from states (projective measurements). *)
Class KAlg `{StAlg} := {
  St_eq_dec (a b : St) : {a = b} + {a <> b};
  (* Distinct outcomes of a measurement lead to distinct states, unless the
      outcome has probability zero. *)
  distinct_outcomes m k k' ρ :
    app (kraus m k) ρ = app (kraus m k') ρ -> k = k' \/ app (kraus m k) ρ = szero }.

Section Kierner.
Context `{KAlg}.

(* ** The MDP, under a history-dependent scheduler

    [hsched] maps the list of states visited so far (most recent first) to
    a choice.  [KV 𝔖 n p ρ h] is the sum, over the 𝔖-induced paths of length
    ≤ n from configuration ⟨p, ρ⟩ with history [h], of their final
    (unnormalised) states: Σ_{ρ'} Pr(◇⟨↓,ρ'⟩) · ρ' truncated at depth n. *)
Definition hsched := list St -> bool.

Fixpoint KV (sc : hsched) n p ρ (h : list St) {struct n} : St :=
  match p, n with
  | Done, _ => ρ
  | _, 0 => szero
  | _, S n =>
      match step p with
      | Leaf K x => KV sc n x (app K ρ) (ρ :: h)
      | Br m xs => ssum (map (fun k => KV sc n (xs k) (app (kraus m k) ρ) (ρ :: h)) (outs m))
      | Ch t x y => KV sc n (if sc (ρ :: h) then y else x) ρ (ρ :: h)
      end
  end.

Definition KVal sc p ρ := ssup (fun n => KV sc n p ρ []).

Lemma KV_S sc n p ρ h : p <> Done -> KV sc (S n) p ρ h =
  match step p with
  | Leaf K x => KV sc n x (app K ρ) (ρ :: h)
  | Br m xs => ssum (map (fun k => KV sc n (xs k) (app (kraus m k) ρ) (ρ :: h)) (outs m))
  | Ch t x y => KV sc n (if sc (ρ :: h) then y else x) ρ (ρ :: h)
  end.
Proof. destruct p; reflexivity || congruence. Qed.

Lemma KV_Done sc n ρ h : KV sc n Done ρ h = ρ.
Proof. destruct n; reflexivity. Qed.

Lemma ssum_szero {A} (l : list A) : ssum (map (fun _ => szero) l) = szero.
Proof. induction l; simpl; [reflexivity | now rewrite IHl, sadd_szero]. Qed.

(* Zero-probability branches contribute nothing, whatever the scheduler. *)
Lemma KV_szero sc n p h : KV sc n p szero h = szero.
Proof.
  induction n in p, h |- *; destruct (done_dec p) as [-> | Hp];
    try (rewrite KV_Done; reflexivity).
  - destruct p; reflexivity || congruence.
  - rewrite KV_S by auto. destruct (step p).
    + now rewrite app_szero, IHn.
    + erewrite map_ext; [apply ssum_szero |]. intro k. now rewrite app_szero, IHn.
    + apply IHn.
Qed.

(* ** Replaying a tag scheduler from the history of states *)

Variable σ : sched.

(* The outcome of measurement [m] that leads from [ρ] to [ρ']. *)
Definition outcome m ρ ρ' :=
  find (fun k => if St_eq_dec (app (kraus m k) ρ) ρ' then true else false) (outs m).

(* One step of the replay: from configuration [q] in state [ρ] to state [ρ']. *)
Definition next q ρ ρ' : option prog :=
  match step q with
  | Leaf _ x => Some x
  | Br m xs => option_map xs (outcome m ρ ρ')
  | Ch t x y => Some (if σ t then y else x)
  end.

(* [replay q l]: the configuration reached from [q] along the states [l]
    (oldest first). *)
Fixpoint replay q (l : list St) : option prog :=
  match l with
  | [] | [_] => Some q
  | ρ :: ((ρ' :: _) as l') =>
      match next q ρ ρ' with Some x => replay x l' | None => None end
  end.

Lemma replay_snoc q l ρ ρ' r :
  replay q (l ++ [ρ]) = Some r -> replay q (l ++ [ρ; ρ']) =
  match next r ρ ρ' with Some x => Some x | None => None end.
Proof.
  induction l as [| a l IH] in q |- *; simpl.
  - intros [= ->]. destruct (next r ρ ρ'); reflexivity.
  - destruct l as [| b l]; simpl in *.
    + destruct (next q a ρ); [apply IH | discriminate].
    + destruct (next q a b); [apply IH | discriminate].
Qed.

Variable p0 : prog.

(* The history-dependent scheduler: replay [p0] and apply [σ] to the tag of
    the current choice. *)
Definition hs : hsched := fun h =>
  match replay p0 (rev h) with
  | Some q => match step q with Ch t _ _ => σ t | _ => false end
  | None => false
  end.

Lemma outcome_spec m ρ k :
  exists k', outcome m ρ (app (kraus m k) ρ) = Some k' /\
             app (kraus m k') ρ = app (kraus m k) ρ.
Proof.
  unfold outcome.
  destruct (find _ (outs m)) as [k' |] eqn:F.
  - exists k'. split; auto. apply find_some in F as [_ F].
    destruct (St_eq_dec _ _) in F; congruence.
  - exfalso. pose proof (find_none _ _ F k (outs_all m k)) as F'. cbv beta in F'.
    destruct (St_eq_dec _ _) in F'; congruence.
Qed.

Lemma KV_hs n q ρ h :
  replay p0 (rev (ρ :: h)) = Some q -> KV hs n q ρ h = app (Op σ n q) ρ.
Proof.
  induction n in q, ρ, h |- *; intro R; destruct (done_dec q) as [-> | Hq].
  1,3: rewrite KV_Done, Op_Done, app_one; reflexivity.
  - rewrite Op_0, app_zero by auto. destruct q; reflexivity || congruence.
  - rewrite KV_S, Op_S by auto.
    assert (Rn : forall ρ', replay p0 (rev (ρ' :: ρ :: h)) = next q ρ ρ').
    { intro ρ'. simpl. rewrite <- app_assoc. simpl.
      rewrite (replay_snoc _ _ _ _ _ R). destruct (next q ρ ρ'); reflexivity. }
    unfold next in Rn. destruct (step q) as [K x | m xs | t x y] eqn:Hs.
    + rewrite app_comp. apply IHn. apply Rn.
    + rewrite br_sum. change (fold_right add zero) with sum.
      rewrite app_ssum, map_map. apply f_equal, map_ext. intro k.
      rewrite app_comp.
      destruct (outcome_spec m ρ k) as (k' & Ek & E).
      destruct (distinct_outcomes m k' k ρ E) as [-> | Z].
      * apply IHn. rewrite Rn, Ek. reflexivity.
      * rewrite <- E, Z, KV_szero, app_szero. reflexivity.
    + assert (C : hs (ρ :: h) = σ t) by (unfold hs; rewrite R, Hs; reflexivity).
      rewrite C. apply IHn. rewrite Rn. reflexivity.
Qed.

(* At every depth, the MDP under [hs] computes the tag-scheduler path sum. *)
Theorem tag_as_history n ρ : KV hs n p0 ρ [] = app (Op σ n p0) ρ.
Proof. apply KV_hs. reflexivity. Qed.

Corollary tag_as_history_val ρ : KVal hs p0 ρ = app (E σ p0) ρ.
Proof.
  unfold KVal, E. symmetry. apply app_sup; [intro; apply Op_mono | intro n; apply tag_as_history].
Qed.

End Kierner.

(* ⊆ of [Kierner, Lemma 3.2]: every element of ⟦p⟧(ρ) is the value of the
    MDP under some history-dependent scheduler. *)
Theorem lifted_in_mdp `{KAlg} (CC : FunctionalCountableChoice_on sched) p x ρ :
  wl p -> Sem p x -> exists sc : hsched, app x ρ = KVal sc p ρ.
Proof.
  intros W Hx. destruct (complete CC p x W Hx) as [σ ->].
  exists (hs σ p). symmetry. apply tag_as_history_val.
Qed.
(* end hide *)
