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

(** * Core Erlang: labelled transition system

    ** Expression level

    As in Lanese et al., the expression semantics answers a /request/ to the
    system level: [e ─ℓ→ e'] where [ℓ ∈ {τ, send(p,v), rec(cls,after),
    spawn(f,v̄), self}] and, for the last three, [e'] contains the hole [κ] that
    the system fills.  The evaluation order of Core Erlang is fixed (left to
    right), so an expression has at most one redex: the relation is a partial
    /function/ [estep], which makes the whole LTS decidable for free.

    ** System level

    A system is a finite multiset of components: processes [⟨p, n, e⟩] (where
    [n] is the number of children [p] has already spawned) and messages in
    transit [⟪p , v⟫].  Parallel composition is multiset union, so the
    structural congruence (associativity, commutativity, unit) is /equality/:
    the harmony lemma has no congruence case to deal with.

    The mailbox of Lanese et al. is not kept per process: messages addressed to
    [p] and not yet consumed stay in transit, and a [receive] consumes any
    matching one.  This is forced by the axioms of the framework and gives up
    the FIFO order of the mailbox; see [Erlang_Design.md] for the argument.

    Actions are [ExtAct (pid * val)]: [ActOut (p,v)] releases a message in
    transit to the environment (non-blocking), [ActIn (p,v)] is the reception
    of [v] by the process [p], which requires a matching clause (blocking). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers gmultiset.
From TestingTheory Require Import ActTau InputOutputActions VACCS Erlang_Syntax.

(** ** The program *)

Class Erlang_Program := MkErlang_Program {
    (** Function definitions: parameters and body. *)
    fun_def : fname → option (list var * expr);
    (** Built-in operations, [eval] of the paper. *)
    bif_eval : bifname → list val → option val;
  }.

(** ** Requests of the expression level *)

Inductive elabel : Type :=
| LTau
| LSend (p : pid) (v : val)
| LRec (cls : clauses) (ao : option expr)
| LSpawn (f : fname) (vs : list val)
| LSelf.

#[global] Instance elabel_eq_dec : EqDecision elabel.
Proof.
  intros l1 l2.
  destruct l1 as [| p1 v1 | cls1 ao1 | f1 vs1 |], l2 as [| p2 v2 | cls2 ao2 | f2 vs2 |];
    try (right; by intros ?; simplify_eq).
  - by left.
  - destruct (decide (p1 = p2)) as [-> |]; [| right; by intros ?; simplify_eq].
    destruct (decide (v1 = v2)) as [-> |]; [by left | right; by intros ?; simplify_eq].
  - destruct (decide (cls1 = cls2)) as [-> |]; [| right; by intros ?; simplify_eq].
    destruct (decide (ao1 = ao2)) as [-> |]; [by left | right; by intros ?; simplify_eq].
  - destruct (decide (f1 = f2)) as [-> |]; [| right; by intros ?; simplify_eq].
    destruct (decide (vs1 = vs2)) as [-> |]; [by left | right; by intros ?; simplify_eq].
  - by left.
Defined.

(** ** Components and systems *)

Inductive comp : Type :=
| CProc (p : pid) (n : nat) (e : expr)
| CMsg (p : pid) (v : val).

#[global] Instance comp_eq_dec : EqDecision comp.
Proof. solve_decision. Defined.

Definition comp_enc (c : comp) : (pid * nat * expr) + (pid * val) :=
  match c with
  | CProc p n e => inl (p, n, e)
  | CMsg p v => inr (p, v)
  end.

Definition comp_dec (x : (pid * nat * expr) + (pid * val)) : comp :=
  match x with
  | inl (p, n, e) => CProc p n e
  | inr (p, v) => CMsg p v
  end.

#[global] Instance comp_countable : Countable comp.
Proof. refine (inj_countable' comp_enc comp_dec _). by intros []. Defined.

(** [sys] is a notation, not a definition: a definition would hide
    [gmultiset comp] from the rewriting of the stdpp lemmas. *)
Notation sys := (gmultiset comp).

Lemma sys_swap (X T S : sys) : T ⊎ (X ⊎ S) = X ⊎ (T ⊎ S).
Proof. multiset_solver. Qed.

Lemma sys_comm (X Y : sys) : X ⊎ Y = Y ⊎ X.
Proof. multiset_solver. Qed.

(** [⟨ p , n , e ⟩] is a process, [⟪ p , v ⟫] a message in transit. *)
Notation "⟨ p , n , e ⟩" := ({[+ CProc p n e +]} : sys) (at level 0).
Notation "⟪ p , v ⟫" := ({[+ CMsg p v +]} : sys) (at level 0).

(** ** Actions *)

(** ** Actions

    The actions are those of VACCS instantiated with [Channel := pid] and
    [Value := val], so that the observers of [VACCS_ta_tc_gen] can be used as
    the test LTS: the framework requires one and the same type of actions for
    the processes and for the tests.  An Erlang system only ever performs
    actions over /closed/ data ([cst]); the open ones ([bvar]) are inert. *)

#[global] Program Instance Erlang_VACCS_Parameters : VACCS_Parameters :=
  {| Channel := pid ; Value := val ; O := VNil |}.

(** As for [sys]: notations, so that the types are never hidden behind a
    constant that the rewriting tactics refuse to unfold. *)
(** [TypeOfActions] is VACCS's [ChannelData * ValueData], here [Data pid * Data
    val]; it is used as such so that every instance of the framework sees one
    and the same type. *)
Notation erl_act := (ExtAct (@TypeOfActions Erlang_VACCS_Parameters)).

(** Notations, not definitions: the proofs then match syntactically. *)
Notation out_act p v := (ActOut (cst p, cst v)).
Notation in_act p v := (ActIn (cst p, cst v)).

Section Erlang_LTS.

Context `{EP : Erlang_Program}.

(** ** The expression semantics as a function *)

Fixpoint args_vals (es : args) : option (list val) :=
  match es with
  | ANil => Some []
  | ACons (EVal v) es' =>
      match args_vals es' with Some vs => Some (v :: vs) | None => None end
  | ACons _ _ => None
  end.

Fixpoint estep (e : expr) : option (elabel * expr) :=
  match e with
  | EVar _ => None
  | EVal _ => None
  | ETick => None
  | EHole => None
  | ESelf => Some (LSelf, EHole)
  | EReceive cls => Some (LRec cls None, EHole)
  | EReceiveAfter cls a => Some (LRec cls (Some a), EHole)
  | ECons e1 e2 =>
      match e1 with
      | EVal v1 =>
          match e2 with
          | EVal v2 => Some (LTau, EVal (VCons v1 v2))
          | _ => match estep e2 with
                 | Some (l, e2') => Some (l, ECons e1 e2')
                 | None => None
                 end
          end
      | _ => match estep e1 with
             | Some (l, e1') => Some (l, ECons e1' e2)
             | None => None
             end
      end
  | ELet x e1 e2 =>
      match e1 with
      | EVal v => Some (LTau, subst [(x, v)] e2)
      | _ => match estep e1 with
             | Some (l, e1') => Some (l, ELet x e1' e2)
             | None => None
             end
      end
  | ECase e0 cls =>
      match e0 with
      | EVal v => match match_cls cls v with
                  | Some e' => Some (LTau, e')
                  | None => None
                  end
      | _ => match estep e0 with
             | Some (l, e0') => Some (l, ECase e0' cls)
             | None => None
             end
      end
  | ESend e1 e2 =>
      match e1 with
      | EVal w =>
          match e2 with
          | EVal v => match w with
                      | VPid p => Some (LSend p v, EVal v)
                      | _ => None
                      end
          | _ => match estep e2 with
                 | Some (l, e2') => Some (l, ESend e1 e2')
                 | None => None
                 end
          end
      | _ => match estep e1 with
             | Some (l, e1') => Some (l, ESend e1' e2)
             | None => None
             end
      end
  | EApply f es =>
      match args_vals es with
      | Some vs =>
          match fun_def f with
          | Some (xs, body) =>
              if decide (length xs = length vs)
              then Some (LTau, subst (zip xs vs) body)
              else None
          | None => None
          end
      | None => match estep_args es with
                | Some (l, es') => Some (l, EApply f es')
                | None => None
                end
      end
  | ECall op es =>
      match args_vals es with
      | Some vs =>
          match bif_eval op vs with
          | Some v => Some (LTau, EVal v)
          | None => None
          end
      | None => match estep_args es with
                | Some (l, es') => Some (l, ECall op es')
                | None => None
                end
      end
  | ESpawn f es =>
      match args_vals es with
      | Some vs => Some (LSpawn f vs, EHole)
      | None => match estep_args es with
                | Some (l, es') => Some (l, ESpawn f es')
                | None => None
                end
      end
  end
with estep_args (es : args) : option (elabel * args) :=
  match es with
  | ANil => None
  | ACons e es' =>
      match e with
      | EVal _ => match estep_args es' with
                  | Some (l, es'') => Some (l, ACons e es'')
                  | None => None
                  end
      | _ => match estep e with
             | Some (l, e') => Some (l, ACons e' es')
             | None => None
             end
      end
  end.

(** ** The transition relation *)

Inductive erl_lts : sys → Act erl_act → sys → Prop :=
(** A local step of an expression. *)
| ErlTau S p n e e' :
  estep e = Some (LTau, e') →
  erl_lts (⟨p, n, e⟩ ⊎ S) τ (⟨p, n, e'⟩ ⊎ S)
(** A send puts a message in transit; self-sending is included. *)
| ErlSend S p n e q v e' :
  estep e = Some (LSend q v, e') →
  erl_lts (⟨p, n, e⟩ ⊎ S) τ (⟨p, n, e'⟩ ⊎ ⟪q , v⟫ ⊎ S)
(** [self()] returns the pid of the process. *)
| ErlSelf S p n e e' :
  estep e = Some (LSelf, e') →
  erl_lts (⟨p, n, e⟩ ⊎ S) τ (⟨p, n, hfill e' (EVal (VPid p))⟩ ⊎ S)
(** [spawn] creates the [n]-th child of [p], whose pid is [n :: p]. *)
| ErlSpawn S p n e f vs e' xs body :
  estep e = Some (LSpawn f vs, e') →
  fun_def f = Some (xs, body) →
  length xs = length vs →
  erl_lts (⟨p, n, e⟩ ⊎ S) τ
    (⟨p, n + 1, hfill e' (EVal (VPid (n :: p)))⟩ ⊎ ⟨n :: p, 0, subst (zip xs vs) body⟩ ⊎ S)
(** The timeout branch of a [receive] may always be taken. *)
| ErlTimeout S p n e cls a e' :
  estep e = Some (LRec cls (Some a), e') →
  erl_lts (⟨p, n, e⟩ ⊎ S) τ (⟨p, n, hfill e' a⟩ ⊎ S)
(** A [receive] consumes a matching message in transit. *)
| ErlComm S p n e cls ao e' v body :
  estep e = Some (LRec cls ao, e') →
  match_cls cls v = Some body →
  erl_lts (⟨p, n, e⟩ ⊎ ⟪p , v⟫ ⊎ S) τ (⟨p, n, hfill e' body⟩ ⊎ S)
(** A [receive] consumes a matching message coming from the environment. *)
| ErlIn S p n e cls ao e' v body :
  estep e = Some (LRec cls ao, e') →
  match_cls cls v = Some body →
  erl_lts (⟨p, n, e⟩ ⊎ S) (ActExt (in_act p v)) (⟨p, n, hfill e' body⟩ ⊎ S)
(** A message in transit may be released to the environment. *)
| ErlOut S p v :
  erl_lts (⟪p , v⟫ ⊎ S) (ActExt (out_act p v)) S
.


(** ** Every rule is closed under parallel composition *)

(** Never use [econstructor] or [eauto] on a goal whose indices are multiset
    expressions: the unifier unfolds [⊎] and diverges.  Always name the rule. *)
Lemma erl_lts_par_l S1 α S2 T : erl_lts S1 α S2 → erl_lts (T ⊎ S1) α (T ⊎ S2).
Proof.
  intros hl. inversion hl; subst.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). by apply ErlTau.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). by apply ErlSend.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). by apply ErlSelf.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). eapply ErlSpawn; eassumption.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). eapply ErlTimeout; eassumption.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). eapply ErlComm; eassumption.
  - rewrite (sys_swap _ T _), (sys_swap _ T _). eapply ErlIn; eassumption.
  - rewrite (sys_swap _ T _). apply ErlOut.
Qed.

Lemma erl_lts_par_r S1 α S2 T : erl_lts S1 α S2 → erl_lts (S1 ⊎ T) α (S2 ⊎ T).
Proof.
  intros hl.
  rewrite (sys_comm S1 T), (sys_comm S2 T).
  by apply erl_lts_par_l.
Qed.

End Erlang_LTS.

Global Hint Constructors erl_lts : erl.

Notation "S ⟶ₑ T" := (erl_lts S τ T) (at level 30).
Notation "S ⟶ₑ{ α } T" := (erl_lts S α T) (at level 30).
Notation "S ⟶ₑ[ μ ] T" := (erl_lts S (ActExt μ) T) (at level 30).

