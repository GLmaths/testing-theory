(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

   This file formalises the syntax from:
   R. De Nicola, R. Pugliese, "Linda-based applicative and imperative
   process algebras", Theoretical Computer Science 238 (2000) 389-437.

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

From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable option gmap.

(** * PAL: syntax

    The syntax of the Linda-based applicative process algebra from:

    R. De Nicola, R. Pugliese, "Linda-based applicative and imperative
    process algebras", Theoretical Computer Science 238 (2000) 389-437.

    Syntax (Definition 3.1), substitutions, tuple evaluation and pattern
    matching (Tables 1-2), with their decidability and countability.  The
    LTSs are built on top of it, in [Applicative_process_algebra.v] and
    [PAL_Alt_LTS.v]. *)

Section PAL_Syntax.
  Context {Val : Type} `{Countable Val}.

  Definition Var := nat.
  Definition PVar := nat.

  (** ** Syntax (Definition 3.1)

      [Exp] and [BExp] are left abstract in the paper (parametrised by an
      external evaluation function [E⟦·⟧]); [vexp]/[bexp] below are a
      minimal concrete stand-in, since [Val] itself is only assumed
      [Countable] here. *)

  (* value expressions: a free variable reference, or a closed value *)
  Inductive vexp :=
    | ve_var (x : Var)
    | ve_val (v : Val).

  (* tuple fields: formal (binds x), actual (an expression), wildcard *)
  Inductive field :=
    | f_formal (x : Var)
    | f_actual (e : vexp)
    | f_star.

  Definition tuple := list field.

  (* boolean expressions, kept minimal (equality tests) since Val is abstract *)
  Inductive bexp :=
    | b_true
    | b_false
    | b_eq (e1 e2 : vexp)
    | b_and (b1 b2 : bexp)
    | b_or (b1 b2 : bexp)
    | b_not (b : bexp).

  Inductive term :=
    | t_nil
    | t_undef
    | t_out (t : tuple) (E : term)
    | t_in (t : tuple) (E : term)
    | t_read (t : tuple) (E : term)
    | t_eval (E1 E2 : term)
    | t_if (be : bexp) (E1 E2 : term)
    | t_ichoice (E1 E2 : term)
    | t_echoice (E1 E2 : term)
    | t_par (E1 E2 : term)
    | t_lmerge (E1 E2 : term)
    | t_cmerge (E1 E2 : term)
    | t_pvar (X : PVar)
    | t_rec (X : PVar) (E : term)
    (* success of an observer (the paper's [success], Section 5) *)
    | t_success.

  (** ** Value-substitution

      Plain (no capture-avoidance): it only ever substitutes *closed
      values* for variables — never expressions with free variables — so
      capture is structurally impossible.  Shadowing under [t_in]/[t_read]
      is handled by dropping the tuple's own formals from the
      substitution ([vsubst_drop]). *)

  Definition vsubst := list (Var * Val).

  Fixpoint vlookup (sigma : vsubst) (x : Var) : option Val :=
    match sigma with
    | [] => None
    | (y,v) :: sigma' => if decide (x = y) then Some v else vlookup sigma' x
    end.

  Definition subst_vexp (sigma : vsubst) (e : vexp) : vexp :=
    match e with
    | ve_val v => ve_val v
    | ve_var x => match vlookup sigma x with Some v => ve_val v | None => ve_var x end
    end.

  Definition subst_field (sigma : vsubst) (f : field) : field :=
    match f with
    | f_formal x => f_formal x
    | f_actual e => f_actual (subst_vexp sigma e)
    | f_star => f_star
    end.

  Definition subst_tuple (sigma : vsubst) (t : tuple) : tuple := map (subst_field sigma) t.

  Fixpoint subst_bexp (sigma : vsubst) (be : bexp) : bexp :=
    match be with
    | b_true => b_true
    | b_false => b_false
    | b_eq e1 e2 => b_eq (subst_vexp sigma e1) (subst_vexp sigma e2)
    | b_and b1 b2 => b_and (subst_bexp sigma b1) (subst_bexp sigma b2)
    | b_or b1 b2 => b_or (subst_bexp sigma b1) (subst_bexp sigma b2)
    | b_not b1 => b_not (subst_bexp sigma b1)
    end.

  Definition tuple_formals (t : tuple) : list Var :=
    omap (fun f => match f with f_formal x => Some x | _ => None end) t.

  Definition vsubst_drop (xs : list Var) (sigma : vsubst) : vsubst :=
    filter (fun p => negb (bool_decide (fst p ∈ xs))) sigma.

  Fixpoint subst_term (sigma : vsubst) (E : term) : term :=
    match E with
    | t_nil => t_nil
    | t_undef => t_undef
    | t_out t E1 => t_out (subst_tuple sigma t) (subst_term sigma E1)
    | t_in t E1 => t_in (subst_tuple sigma t) (subst_term (vsubst_drop (tuple_formals t) sigma) E1)
    | t_read t E1 => t_read (subst_tuple sigma t) (subst_term (vsubst_drop (tuple_formals t) sigma) E1)
    | t_eval E1 E2 => t_eval (subst_term sigma E1) (subst_term sigma E2)
    | t_if be E1 E2 => t_if (subst_bexp sigma be) (subst_term sigma E1) (subst_term sigma E2)
    | t_ichoice E1 E2 => t_ichoice (subst_term sigma E1) (subst_term sigma E2)
    | t_echoice E1 E2 => t_echoice (subst_term sigma E1) (subst_term sigma E2)
    | t_par E1 E2 => t_par (subst_term sigma E1) (subst_term sigma E2)
    | t_lmerge E1 E2 => t_lmerge (subst_term sigma E1) (subst_term sigma E2)
    | t_cmerge E1 E2 => t_cmerge (subst_term sigma E1) (subst_term sigma E2)
    | t_pvar X => t_pvar X
    | t_rec X E1 => t_rec X (subst_term sigma E1)
    | t_success => t_success
    end.

  (* substitute term Q for process variable X throughout E; plain (no renaming),
     matching the paper's own restriction to well-formed PAL terms (Definition 3.1)
     where no capture can arise from unfolding [rec X.E] into [E[rec X.E/X]] *)
  Fixpoint psubst (X : PVar) (Q : term) (E : term) : term :=
    match E with
    | t_nil => t_nil
    | t_undef => t_undef
    | t_out t E1 => t_out t (psubst X Q E1)
    | t_in t E1 => t_in t (psubst X Q E1)
    | t_read t E1 => t_read t (psubst X Q E1)
    | t_eval E1 E2 => t_eval (psubst X Q E1) (psubst X Q E2)
    | t_if be E1 E2 => t_if be (psubst X Q E1) (psubst X Q E2)
    | t_ichoice E1 E2 => t_ichoice (psubst X Q E1) (psubst X Q E2)
    | t_echoice E1 E2 => t_echoice (psubst X Q E1) (psubst X Q E2)
    | t_par E1 E2 => t_par (psubst X Q E1) (psubst X Q E2)
    | t_lmerge E1 E2 => t_lmerge (psubst X Q E1) (psubst X Q E2)
    | t_cmerge E1 E2 => t_cmerge (psubst X Q E1) (psubst X Q E2)
    | t_pvar Y => if decide (X = Y) then Q else t_pvar Y
    | t_rec Y E1 => if decide (X = Y) then t_rec Y E1 else t_rec Y (psubst X Q E1)
    | t_success => t_success
    end.

  (** ** Tuple evaluation and matching (Tables 1-2) *)

  (* evaluated output/input tuples: Table 1 *)
  Inductive out_field := of_star | of_val (v : Val).

  Definition eot := list out_field.

  Inductive in_field := if_formal (x : Var) | if_val (v : Val) | if_star.

  Definition eit := list in_field.

  (* O and I: partial (undefined on non-closed actual fields), Table 1 *)
  Definition eval_out_field (f : field) : option out_field :=
    match f with
    | f_formal _ => Some of_star
    | f_star => Some of_star
    | f_actual (ve_val v) => Some (of_val v)
    | f_actual (ve_var _) => None
    end.

  Definition eval_out_tuple (t : tuple) : option eot := mapM eval_out_field t.

  Definition eval_in_field (f : field) : option in_field :=
    match f with
    | f_formal x => Some (if_formal x)
    | f_star => Some if_star
    | f_actual (ve_val v) => Some (if_val v)
    | f_actual (ve_var _) => None
    end.

  Definition eval_in_tuple (t : tuple) : option eit := mapM eval_in_field t.

  (* Pattern matching, Table 2 *)
  Inductive field_match : in_field -> out_field -> Prop :=
    | fm_val (v : Val) : field_match (if_val v) (of_val v)
    | fm_var (x : Var) (v : Val) : field_match (if_formal x) (of_val v)
    | fm_star : field_match if_star of_star.

  Inductive tuple_match : eit -> eot -> Prop :=
    | tm_nil : tuple_match [] []
    | tm_cons f1 f2 it ot :
        field_match f1 f2 -> tuple_match it ot -> tuple_match (f1 :: it) (f2 :: ot).

  (* the substitution [ot/I[t]] built from a matched pair, Rule AR1/AR2 *)
  Fixpoint build_subst (it : eit) (ot : eot) : vsubst :=
    match it, ot with
    | if_formal x :: it', of_val v :: ot' => (x, v) :: build_subst it' ot'
    | _ :: it', _ :: ot' => build_subst it' ot'
    | _, _ => []
    end.

  Definition eot_to_tuple (ot : eot) : tuple :=
    map (fun of => match of with of_val v => f_actual (ve_val v) | of_star => f_star end) ot.

  Fixpoint eval_bexp (be : bexp) : option bool :=
    match be with
    | b_true => Some true
    | b_false => Some false
    | b_eq e1 e2 =>
        match e1, e2 with
        | ve_val v1, ve_val v2 => Some (bool_decide (v1 = v2))
        | _, _ => None
        end
    | b_and b1 b2 =>
        match eval_bexp b1, eval_bexp b2 with
        | Some r1, Some r2 => Some (r1 && r2) | _, _ => None end
    | b_or b1 b2 =>
        match eval_bexp b1, eval_bexp b2 with
        | Some r1, Some r2 => Some (r1 || r2) | _, _ => None end
    | b_not b1 =>
        match eval_bexp b1 with Some r1 => Some (negb r1) | None => None end
    end.

  #[global] Instance vexp_eqdec : EqDecision vexp.
  Proof. solve_decision. Defined.

  #[global] Instance field_eqdec : EqDecision field.
  Proof. solve_decision. Defined.

  #[global] Instance bexp_eqdec : EqDecision bexp.
  Proof. solve_decision. Defined.

  #[global] Instance term_eqdec : EqDecision term.
  Proof. solve_decision. Defined.

  #[global] Instance out_field_eqdec : EqDecision out_field.
  Proof. solve_decision. Defined.

  #[global] Instance in_field_eqdec : EqDecision in_field.
  Proof. solve_decision. Defined.
  Definition field_match_b (f1 : in_field) (f2 : out_field) : bool :=
    match f1, f2 with
    | if_val v, of_val v' => bool_decide (v = v')
    | if_formal _, of_val _ => true
    | if_star, of_star => true
    | _, _ => false
    end.

  Fixpoint tuple_match_b (it : eit) (ot : eot) : bool :=
    match it, ot with
    | [], [] => true
    | f1 :: it', f2 :: ot' => field_match_b f1 f2 && tuple_match_b it' ot'
    | _, _ => false
    end.

  Lemma field_match_b_correct f1 f2 : field_match_b f1 f2 = true <-> field_match f1 f2.
  Proof.
    split.
    - intro H1.
      destruct f1, f2; simpl in H1; try discriminate; try constructor.
      apply bool_decide_eq_true in H1.
      subst.
      constructor.
    - intro H1.
      destruct H1; simpl; [apply bool_decide_eq_true; reflexivity | reflexivity | reflexivity].
  Qed.

  Lemma tuple_match_b_correct it ot : tuple_match_b it ot = true <-> tuple_match it ot.
  Proof.
    revert ot.
    induction it as [| f1 it' IH]; intros ot; destruct ot as [| f2 ot']; simpl.
    - split; [constructor | reflexivity].
    - split; [discriminate | intro H1; inversion H1].
    - split; [discriminate | intro H1; inversion H1].
    - rewrite andb_true_iff, field_match_b_correct, IH.
      split.
      + intros [H1 H2]. constructor; assumption.
      + intro H1. inversion H1; subst. split; assumption.
  Qed.
  #[global] Instance out_field_countable : Countable out_field.
  Proof.
    refine (inj_countable
      (fun f => match f with of_star => None | of_val v => Some v end)
      (fun o => match o with None => Some of_star | Some v => Some (of_val v) end)
      _).
    intros []; reflexivity.
  Defined.

  #[global] Instance eot_countable : Countable eot := _.

  (** ** [Countable term]

      Needed for [FiniteImagegLts]/[coFiniteImagegLts]/[Prop_of_Inter]'s
      [gset]s.  Built the same way as every other calculus in this
      project (cf. [CCSInstance.v]'s [proc_count]): a [gen_tree]
      encode/decode pair, here over the leaf type [Var + Val], with
      [vexp]/[field]/[tuple]/[bexp] encoded first since [term] embeds
      them. *)

  Definition encode_vexp (e : vexp) : gen_tree (Var + Val) :=
    match e with
    | ve_var x => GenNode 0 [GenLeaf (inl x)]
    | ve_val v => GenNode 1 [GenLeaf (inr v)]
    end.

  Definition decode_vexp (t : gen_tree (Var + Val)) : option vexp :=
    match t with
    | GenNode 0 [GenLeaf (inl x)] => Some (ve_var x)
    | GenNode 1 [GenLeaf (inr v)] => Some (ve_val v)
    | _ => None
    end.

  Lemma encode_decode_vexp e : decode_vexp (encode_vexp e) = Some e.
  Proof. destruct e; reflexivity. Qed.

  #[global] Instance vexp_countable : Countable vexp.
  Proof. refine (inj_countable encode_vexp decode_vexp encode_decode_vexp). Defined.

  Definition encode_field (f : field) : gen_tree (Var + Val) :=
    match f with
    | f_formal x => GenNode 0 [GenLeaf (inl x)]
    | f_actual e => GenNode 1 [encode_vexp e]
    | f_star => GenNode 2 []
    end.

  Definition decode_field (t : gen_tree (Var + Val)) : option field :=
    match t with
    | GenNode 0 [GenLeaf (inl x)] => Some (f_formal x)
    | GenNode 1 [te] => e ← decode_vexp te; Some (f_actual e)
    | GenNode 2 [] => Some f_star
    | _ => None
    end.

  Lemma encode_decode_field f : decode_field (encode_field f) = Some f.
  Proof.
    destruct f; simpl; [reflexivity | rewrite encode_decode_vexp; reflexivity | reflexivity].
  Qed.

  #[global] Instance field_countable : Countable field.
  Proof. refine (inj_countable encode_field decode_field encode_decode_field). Defined.

  #[global] Instance tuple_countable : Countable tuple := _.

  Fixpoint encode_bexp (be : bexp) : gen_tree (Var + Val) :=
    match be with
    | b_true => GenNode 0 []
    | b_false => GenNode 1 []
    | b_eq e1 e2 => GenNode 2 [encode_vexp e1; encode_vexp e2]
    | b_and b1 b2 => GenNode 3 [encode_bexp b1; encode_bexp b2]
    | b_or b1 b2 => GenNode 4 [encode_bexp b1; encode_bexp b2]
    | b_not b1 => GenNode 5 [encode_bexp b1]
    end.

  Fixpoint decode_bexp (t : gen_tree (Var + Val)) : option bexp :=
    match t with
    | GenNode 0 [] => Some b_true
    | GenNode 1 [] => Some b_false
    | GenNode 2 [t1; t2] => e1 ← decode_vexp t1; e2 ← decode_vexp t2; Some (b_eq e1 e2)
    | GenNode 3 [t1; t2] => b1 ← decode_bexp t1; b2 ← decode_bexp t2; Some (b_and b1 b2)
    | GenNode 4 [t1; t2] => b1 ← decode_bexp t1; b2 ← decode_bexp t2; Some (b_or b1 b2)
    | GenNode 5 [t1] => b1 ← decode_bexp t1; Some (b_not b1)
    | _ => None
    end.

  Lemma encode_decode_bexp be : decode_bexp (encode_bexp be) = Some be.
  Proof.
    induction be; simpl;
      repeat match goal with
      | |- context [decode_vexp (encode_vexp ?e)] => rewrite (encode_decode_vexp e)
      | H : decode_bexp (encode_bexp ?b) = Some ?b |- context [decode_bexp (encode_bexp ?b)] => rewrite H
      end; reflexivity.
  Qed.

  #[global] Instance bexp_countable : Countable bexp.
  Proof. refine (inj_countable encode_bexp decode_bexp encode_decode_bexp). Defined.

  Definition encode_tuple (t : tuple) : gen_tree (Var + Val) := GenNode 0 (map encode_field t).

  Fixpoint decode_tuple_list (ts : list (gen_tree (Var + Val))) : option (list field) :=
    match ts with
    | [] => Some []
    | t :: ts' => f ← decode_field t; fs ← decode_tuple_list ts'; Some (f :: fs)
    end.

  Definition decode_tuple (t : gen_tree (Var + Val)) : option tuple :=
    match t with GenNode 0 ts => decode_tuple_list ts | _ => None end.

  Lemma decode_tuple_list_map t : decode_tuple_list (map encode_field t) = Some t.
  Proof. induction t; simpl; [reflexivity | rewrite encode_decode_field, IHt; reflexivity]. Qed.

  Lemma encode_decode_tuple t : decode_tuple (encode_tuple t) = Some t.
  Proof. unfold decode_tuple, encode_tuple. apply decode_tuple_list_map. Qed.

  Fixpoint encode_term (E : term) : gen_tree (Var + Val) :=
    match E with
    | t_nil => GenNode 0 []
    | t_undef => GenNode 1 []
    | t_out t E1 => GenNode 2 [encode_tuple t; encode_term E1]
    | t_in t E1 => GenNode 3 [encode_tuple t; encode_term E1]
    | t_read t E1 => GenNode 4 [encode_tuple t; encode_term E1]
    | t_eval E1 E2 => GenNode 5 [encode_term E1; encode_term E2]
    | t_if be E1 E2 => GenNode 6 [encode_bexp be; encode_term E1; encode_term E2]
    | t_ichoice E1 E2 => GenNode 7 [encode_term E1; encode_term E2]
    | t_echoice E1 E2 => GenNode 8 [encode_term E1; encode_term E2]
    | t_par E1 E2 => GenNode 9 [encode_term E1; encode_term E2]
    | t_lmerge E1 E2 => GenNode 10 [encode_term E1; encode_term E2]
    | t_cmerge E1 E2 => GenNode 11 [encode_term E1; encode_term E2]
    | t_pvar X => GenNode 12 [GenLeaf (inl X)]
    | t_rec X E1 => GenNode 13 [GenLeaf (inl X); encode_term E1]
    | t_success => GenNode 14 []
    end.

  Fixpoint decode_term (t : gen_tree (Var + Val)) : option term :=
    match t with
    | GenNode 0 [] => Some t_nil
    | GenNode 1 [] => Some t_undef
    | GenNode 2 [gt; te] => tp ← decode_tuple gt; E1 ← decode_term te; Some (t_out tp E1)
    | GenNode 3 [gt; te] => tp ← decode_tuple gt; E1 ← decode_term te; Some (t_in tp E1)
    | GenNode 4 [gt; te] => tp ← decode_tuple gt; E1 ← decode_term te; Some (t_read tp E1)
    | GenNode 5 [te1; te2] => E1 ← decode_term te1; E2 ← decode_term te2; Some (t_eval E1 E2)
    | GenNode 6 [tb; te1; te2] => be ← decode_bexp tb; E1 ← decode_term te1; E2 ← decode_term te2; Some (t_if be E1 E2)
    | GenNode 7 [te1; te2] => E1 ← decode_term te1; E2 ← decode_term te2; Some (t_ichoice E1 E2)
    | GenNode 8 [te1; te2] => E1 ← decode_term te1; E2 ← decode_term te2; Some (t_echoice E1 E2)
    | GenNode 9 [te1; te2] => E1 ← decode_term te1; E2 ← decode_term te2; Some (t_par E1 E2)
    | GenNode 10 [te1; te2] => E1 ← decode_term te1; E2 ← decode_term te2; Some (t_lmerge E1 E2)
    | GenNode 11 [te1; te2] => E1 ← decode_term te1; E2 ← decode_term te2; Some (t_cmerge E1 E2)
    | GenNode 12 [GenLeaf (inl X)] => Some (t_pvar X)
    | GenNode 13 [GenLeaf (inl X); te] => E1 ← decode_term te; Some (t_rec X E1)
    | GenNode 14 [] => Some t_success
    | _ => None
    end.

  Lemma encode_decode_term E : decode_term (encode_term E) = Some E.
  Proof.
    induction E; simpl;
      repeat match goal with
      | |- context [decode_tuple_list (map encode_field ?t)] => rewrite (decode_tuple_list_map t)
      | |- context [decode_bexp (encode_bexp ?b)] => rewrite (encode_decode_bexp b)
      | H : decode_term (encode_term ?E) = Some ?E |- context [decode_term (encode_term ?E)] => rewrite H
      end; reflexivity.
  Qed.

  #[global] Instance term_countable : Countable term.
  Proof. refine (inj_countable encode_term decode_term encode_decode_term). Defined.
End PAL_Syntax.

Arguments vexp Val : clear implicits.
Arguments field Val : clear implicits.
Arguments tuple Val : clear implicits.
Arguments bexp Val : clear implicits.
Arguments term Val : clear implicits.
Arguments vsubst Val : clear implicits.
Arguments out_field Val : clear implicits.
Arguments eot Val : clear implicits.
Arguments in_field Val : clear implicits.
Arguments eit Val : clear implicits.

(** ** Notations, mirroring the paper's own concrete syntax

    Kept in a dedicated scope ([pal_scope]/[%pal]) rather than opened
    globally, since some of the paper's own symbols are already taken
    by the ambient libraries here: [[]] is [ListNotations]'s empty
    list, and a bare [if _ then _ else _] would otherwise shadow every
    plain [bool]/[option] match used throughout this file's own proofs.
    Two deviations from the paper's literal ASCII, for the same
    parser-level reason: prefixing uses [•] instead of [.] (a
    bare-dot-space is Rocq's own sentence terminator, so [a.E] is not
    writable at the top level), and external choice uses [□] instead
    of [[]] (already the empty list). Used by the LTSs for the rules of
    Tables 3-4. *)

Declare Scope pal_scope.
Delimit Scope pal_scope with pal.

Notation "'𝟘'" := t_nil : pal_scope.                                   (* paper: nil *)
Notation "'Ω'" := t_undef : pal_scope.
Notation "'out(' t ')' • E" := (t_out t E) (at level 50) : pal_scope.   (* paper: out(t).E *)
Notation "'in(' t ')' • E" := (t_in t E) (at level 50) : pal_scope.     (* paper: in(t).E *)
Notation "'read(' t ')' • E" := (t_read t E) (at level 50) : pal_scope. (* paper: read(t).E *)
Notation "'eval(' E1 ')' • E2" := (t_eval E1 E2) (at level 50) : pal_scope. (* paper: eval(E).E' *)
Notation "'IF' be 'THEN' E1 'ELSE' E2" := (t_if be E1 E2) (at level 50) : pal_scope. (* paper: if be then E1 else E2 *)
Notation "E1 ⊕ E2" := (t_ichoice E1 E2) (at level 50) : pal_scope.
Notation "E1 □ E2" := (t_echoice E1 E2) (at level 50) : pal_scope.      (* paper: E1 [] E2 *)
Notation "E1 ‖ E2" := (t_par E1 E2) (at level 50) : pal_scope.
Notation "E1 ⌊ E2" := (t_lmerge E1 E2) (at level 50) : pal_scope.
Notation "E1 '|ₖ' E2" := (t_cmerge E1 E2) (at level 50) : pal_scope.    (* paper: E1 |k E2 *)
Notation "'rec' X • E" := (t_rec X E) (at level 50) : pal_scope.        (* paper: rec X.E *)
Notation "'✓'" := t_success : pal_scope.                               (* paper: success *)

Notation "? x" := (f_formal x) (at level 20) : pal_scope.
Notation "! e" := (f_actual e) (at level 20) : pal_scope.
Notation "⋆" := f_star : pal_scope.
