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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list numbers.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.General_definition.Parallel_choice_LTS lqCCS.Language.LTS_quantum_mem lqCCS.Language.LTS_lqCCS_prog lqCCS.Language.LTS_lqCCS_process lqCCS.Language.LTS_lqCCS_par_Qmem lqCCS.Testing.Scheduled.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section LqP.
  Context `{LP : lqCCS_Parameters}.

(* ** Tags with their kinds *)

Inductive okind : Type := KTau | KOut | KIn | KOp | KMeas | KInit | KRec.

#[global] Instance okind_eq_dec : EqDecision okind.
Proof. solve_decision. Defined.

Definition prefix_tagged (𝜆 : prefix) : tag * okind :=
  match 𝜆 with
  | t ∶ 𝛕 => (t, KTau)
  | t ∶ _ ? => (t, KIn)
  | POp t _ _ => (t, KOp)
  | t ∶ _ ⦅_ ▷⦆ => (t, KMeas)
  | PReinit t _ => (t, KInit)
  end.

Fixpoint tagged (P : proc) : list (tag * okind) :=
  match P with
  | PSend t _ _ => [(t, KOut)]
  | If _ Then P Else Q | P ∥ Q => tagged P ++ tagged Q
  | ν P => tagged P
  | PVar _ => []
  | t ∶ rec ∙ P => (t, KRec) :: tagged P
  | PG g => gtagged g
  end
with gtagged (g : guard) : list (tag * okind) :=
  match g with
  | 𝟘{_} | 𝟙 => []
  | 𝜆 ∙ P => prefix_tagged 𝜆 :: tagged P
  | (g1 + g2)%lq => gtagged g1 ++ gtagged g2
  end.

Definition tags (P : proc) : list tag := map fst (tagged P).

(* ** The class of observers *)

Fixpoint obsb (T : proc) : bool :=
  match T with
  | PSend _ _ _ => true
  | If _ Then P Else Q | P ∥ Q => obsb P && obsb Q
  | ν _ | PVar _ | _ ∶ rec ∙ _ => false
  | PG g => gobsb g
  end
with gobsb (g : guard) : bool :=
  match g with
  | 𝟘{_} | 𝟙 => true
  | _ ∶ 𝛕 ∙ _ => false
  | _ ∙ P => obsb P
  | (g1 + g2)%lq => gobsb g1 && gobsb g2 && negb (gsuccessb g1 || gsuccessb g2)
  end.

Fixpoint out_chans (T : proc) : list channel :=
  match T with
  | PSend _ c _ => [c]
  | If _ Then P Else Q | P ∥ Q => out_chans P ++ out_chans Q
  | ν P | _ ∶ rec ∙ P => out_chans P
  | PVar _ => []
  | PG g => gout_chans g
  end
with gout_chans (g : guard) : list channel :=
  match g with
  | 𝟘{_} | 𝟙 => []
  | _ ∙ P => out_chans P
  | (g1 + g2)%lq => gout_chans g1 ++ gout_chans g2
  end.

Fixpoint in_chans (T : proc) : list channel :=
  match T with
  | PSend _ _ _ | PVar _ => []
  | If _ Then P Else Q | P ∥ Q => in_chans P ++ in_chans Q
  | ν P | _ ∶ rec ∙ P => in_chans P
  | PG g => gin_chans g
  end
with gin_chans (g : guard) : list channel :=
  match g with
  | 𝟘{_} | 𝟙 => []
  | _ ∶ c ? ∙ P => c :: in_chans P
  | _ ∙ P => in_chans P
  | (g1 + g2)%lq => gin_chans g1 ++ gin_chans g2
  end.

Definition chan_disjoint (T : proc) : Prop := ∀ c, c ∈ out_chans T → c ∉ in_chans T.

Definition obs (T : proc) : Prop := obsb T = true ∧ chan_disjoint T.

(* ** Recursive observers *)

Fixpoint obsrb (T : proc) : bool :=
  match T with
  | PSend _ _ _ | PVar _ => true
  | If _ Then P Else Q | P ∥ Q => obsrb P && obsrb Q
  | ν _ => false
  | _ ∶ rec ∙ P => obsrb P
  | PG g => gobsrb g
  end
with gobsrb (g : guard) : bool :=
  match g with
  | 𝟘{_} | 𝟙 => true
  | _ ∶ 𝛕 ∙ _ => false
  | _ ∙ P => obsrb P
  | (g1 + g2)%lq => gobsrb g1 && gobsrb g2 && negb (gsuccessb g1 || gsuccessb g2)
  end.

Definition obsr (T : proc) : Prop := obsrb T = true ∧ chan_disjoint T.

End LqP.

(* end hide *)
