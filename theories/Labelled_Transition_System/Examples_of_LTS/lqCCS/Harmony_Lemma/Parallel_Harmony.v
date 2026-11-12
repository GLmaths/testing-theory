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
(* * Parallel harmony: [⟨ρ, P ∥ Q⟩ -τ->_s ⟨ρ', P' ∥ Q'⟩ ↔ ((ρ ∣ P) ∣ Q) -τ->_s ((ρ' ∣ P') ∣ Q')]

    The configuration of a parallel composition [P ∥ Q] is the composition
    of the system [ρ ∣ P] (memory and program, [sync]) with the program [Q],
    for [sync_sys]: [Q] synchronises with the memory of the system
    ([sync]) and with the channels of [P] ([sync_chan]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States pMust_almost_sure lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Harmony_Lemma.Memory_Harmony.

#[local] Open Scope lqccs_scope.

Section Par_Harmony.
  Context `{QM : QuantumModel}.

  Theorem parallel_harmony ρ P Q s ρ' R :
    conf_step ρ (P ∥ Q) s τ ρ' R
    ↔ ∃ P' Q', R = P' ∥ Q'
               ∧ ((mem_step ∣[sync] prog_step) ∣[sync_sys] prog_step) ((ρ, P), Q) s τ ((ρ', P'), Q').
  Proof.
    split.
    - intros Hc.
      inversion Hc as [| | | |? ? ? ? ? P' HP|? ? ? ? ? Q' HQ
                      |? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |]; subst.
      + exists P', Q. split; [done|].
        apply pre_harmony in HP.
        exact (par_left _ prog_step sync_sys (ρ, P) Q s τ (ρ', P') HP).
      + exists P, Q'. split; [done|].
        destruct (conf_step_tau_inv _ _ _ _ _ HQ) as [(Hp & ->) | (t & a & b & -> & Hp & Hm & Hs)].
        * exact (par_right (mem_step ∣[sync] prog_step) prog_step sync_sys (ρ, P) Q s τ Q' Hp).
        * eapply (par_sync _ _ _ (ρ, P) Q CEps (CTag t) (CTag t) (inl b) a).
          -- exact (par_left mem_step prog_step sync ρ P CEps (ActExt b) ρ' Hm).
          -- exact Hp.
          -- by constructor.
          -- constructor.
      + exists P', Q'. split; [done|].
        destruct (conf_step_ext_inv _ _ _ _ _ _ HP) as (_ & HpP & _).
        destruct (conf_step_ext_inv _ _ _ _ _ _ HQ) as (_ & HpQ & _).
        eapply (par_sync _ _ _ (ρ', P) Q (CTag t) (CTag t') (cpair t t') (inr (PrOut c v)) (PrIn c v)).
        -- exact (par_right mem_step prog_step sync ρ' P (CTag t) (ActExt (PrOut c v)) P' HpP).
        -- exact HpQ.
        -- by do 2 constructor.
        -- constructor.
      + exists P', Q'. split; [done|].
        destruct (conf_step_ext_inv _ _ _ _ _ _ HP) as (_ & HpP & _).
        destruct (conf_step_ext_inv _ _ _ _ _ _ HQ) as (_ & HpQ & _).
        eapply (par_sync _ _ _ (ρ', P) Q (CTag t) (CTag t') (cpair t t') (inr (PrIn c v)) (PrOut c v)).
        -- exact (par_right mem_step prog_step sync ρ' P (CTag t) (ActExt (PrIn c v)) P' HpP).
        -- exact HpQ.
        -- by do 2 constructor.
        -- constructor.
    - intros (P' & Q' & -> & Hp).
      inversion Hp as [? ? ? l ? Hl El | ? ? ? l ? Hq El | ? ? c1 c2 ? μ1 μ2 ? ? Hl Hq Hs Hm]; subst.
      + destruct l; [discriminate|]. simplify_eq.
        apply co_parL. by apply pre_harmony.
      + destruct l; [discriminate|]. simplify_eq.
        apply co_parR. by apply prog_step_tau_conf.
      + inversion Hl as [? ? ? l ? Hm' | ? ? ? l ? Hp' |]; subst.
        * destruct l as [b|]; simpl in *; simplify_eq.
          destruct (mem_step_choice _ _ _ _ Hm') as (-> & _).
          rewrite (cmul_eps_l_inv _ _ Hm).
          inversion Hs; subst.
          apply co_parR. by eapply prog_step_mem_conf.
        * destruct l as [a|]; simpl in *; simplify_eq.
          inversion Hs as [|? ? Hch]; subst.
          destruct (prog_step_ext_choice _ _ _ _ Hp') as (t & ->).
          destruct (prog_step_ext_choice _ _ _ _ Hq) as (t' & ->).
          inversion Hm; subst.
          inversion Hch; subst.
          -- eapply co_syncL; apply prog_step_ext_conf; try done; by do 2 eexists; eauto.
          -- eapply co_syncR; apply prog_step_ext_conf; try done; by do 2 eexists; eauto.
  Qed.
End Par_Harmony.
(* end hide *)
