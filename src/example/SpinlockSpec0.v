From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import Spinlock.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic SCMemSpec.
From Fairness Require Import OneShotsRA AuthExclsRA.

Section SPEC.

  Context {src_state : Type}.
  Context {src_ident : Type}.
  Context {Client : Mod.t}.
  Context {gvs : list nat}.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.

  Context `{sub : @SRA.subG Γ Σ}.
  Context {TLRASs : TLRAs_small STT Γ}.
  Context {TLRAS : TLRAs STT Γ Σ}.

  Context {HasMEMRA: @GRA.inG memRA Γ}.
  Context {HasOneShots : @GRA.inG (OneShots.t unit) Γ}.
  Context {HasAuthExcl2 : @GRA.inG (AuthExcls.t (nat * nat)) Γ}.

  Ltac red_tl_all := red_tl; red_tl_memra; red_tl_authexcls; red_tl_oneshots.

  Context (spinlockN : namespace) `{DISJ: (↑N_state_tgt :coPset) ## (↑spinlockN : coPset)}.

  (** Invariants. *)
  Definition spinlockInv (n : nat) κs (x : SCMem.val) (γl : nat) (P : sProp n)
    : sProp n :=
    (∃ (γκu κu : τ{nat}),
        (● γl (γκu, κu))
          ∗
          (((x ↦ 0) ∗ (○ γl (γκu, κu)) ∗ P)
           ∨ ((x ↦ 1) ∗ (△ γκu 1) ∗ (-[κu](0)-◇ (▿ γκu tt)) ∗ (κu -(0)-◇ κs)))
    )%S.

  Definition isSpinlock n κs (x : SCMem.val) (γl : nat) (P : sProp n) (ℓL μn : nat)
    : sProp n :=
    (◆[κs, ℓL, μn] ∗ syn_inv n spinlockN (spinlockInv n κs x γl P))%S.

  Global Instance isSpinlock_persistent n κs (x : SCMem.val) (γl : nat) (P : sProp n) ℓL μn :
    Persistent (⟦isSpinlock n κs x γl P ℓL μn, n⟧).
  Proof.
    unfold Persistent. iIntros "H". unfold isSpinlock. red_tl.
    rewrite red_syn_inv. iDestruct "H" as "#H". auto.
  Qed.

  Lemma isSpinlock_unfold
        n κs (x : SCMem.val) (γl : nat) (P : sProp n) (ℓL μn : nat)
    :
    ⟦(isSpinlock n κs x γl P ℓL μn), n⟧
      ⊢ (◆[κs, ℓL, μn] ∗ inv n spinlockN (spinlockInv n κs x γl P))%I.
  Proof.
    unfold isSpinlock. red_tl. rewrite red_syn_inv. iIntros "[A B]". iFrame.
  Qed.

  Lemma pass_lock
        n κs (x : SCMem.val) (γl : nat) (P : sProp n) (ℓL μn : nat)
        tid γκu κu ϕ
        ℓl μa γκu' κu'
        E
        (SUB : (↑spinlockN) ⊆ E)
    :
    ⊢
      (⟦((isSpinlock n κs x γl P ℓL μn)
           ∗ (○ γl (γκu, κu)) ∗ (Duty(tid) ((κu, 0, ▿ γκu tt) :: ϕ))
           ∗ ◇[κs](ℓl, μa)
           ∗ ◆[κu', ℓl, μa] ∗ ⧖[κu', (1/2)] ∗ (△ γκu' 1) ∗ (-[κu'](0)-⧖ (▿ γκu' tt))
        )%S, n⟧)
      =|1+n|=(⟦syn_fairI (1+n), 1+n⟧)={E}=∗ (⟦((○ γl (γκu', κu')) ∗ (Duty(tid) ϕ) ∗ (▿ γκu tt) ∗ (⋈[κu']))%S, n⟧).
  Proof.
    rewrite red_syn_fairI. red_tl_all. simpl.
    iIntros "(#ISL & LK & DUTY & PCs & #LOu' & POu' & PENDu' & DPu')".
    iPoseProof (isSpinlock_unfold with "ISL") as "[_ #INV_SL]".
    iInv "INV_SL" as "SL" "INV_SL_CL".
    iEval (simpl; unfold spinlockInv; red_tl_all) in "SL".
    iDestruct "SL" as "[%γκu0 SL]". iEval (red_tl) in "SL".
    iDestruct "SL" as "[%κu0 SL]". iEval (red_tl) in "SL".
    iEval (red_tl_all; simpl) in "SL".
    iDestruct "SL" as "(LKb & CASES)".
    iPoseProof (AuthExcls.b_w_eq with "LKb LK") as "%EQ". inv EQ.
    iDestruct "CASES" as "[(_ & LK2 & _) | (PTx & PENDu & PRu & LINKu)]".
    { iExFalso. iPoseProof (AuthExcls.w_w_false with "LK LK2") as "%F". inv F. }
    iMod (OneShots.pending_shot _ tt with "PENDu") as "#SHOTu".
    iPoseProof (unfold_tpromise with "PRu") as "[_ #ACTu]".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. iEval (simpl; red_tl_all). auto. }
    iMod (activate_tpromise with "DPu' POu'") as "[#PRu' ACTu']".
    iMod (link_new_fine _ _ _ _ 0 with "[PCs]") as "#LINKu'".
    { iSplitR. iApply "LOu'". iFrame. }
    iMod (AuthExcls.b_w_update _ _ _ (γκu', κu') with "LKb LK") as "[LKb LK]".
    iMod ("INV_SL_CL" with "[PENDu' PTx LKb]") as "_".
    { iEval (unfold spinlockInv; simpl; red_tl_all).
      iExists γκu'. iEval (red_tl). iExists κu'.
      iEval (red_tl_all; simpl). iFrame. iRight. iFrame. auto.
    }
    iModIntro. iFrame. auto.
  Qed.

  Lemma Spinlock_lock_spec
        tid n
    :
    ⊢ ∀ κs x γl (P : sProp n) ℓL μn (ds : list (nat * nat * sProp n)) ℓu μu,
      (⌜0 < ℓu⌝) →
        [@ tid, n, ⊤ @]
          ⧼⟦((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isSpinlock n κs x γl P ℓL μn)
               ∗ ◇[κs](ℓu, 1 + μu)
               ∗ (⤉ Duty(tid) ds)
               ∗ ◇{ds@1}(1 + ℓL, μn)
               ∗ ◇{ds@1}(1, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock x))
            ⧼rv, ⟦(∃ (γκu κu : τ{nat, 1+n}),
                      (⤉ ○ γl (γκu, κu))
                        ∗ (⤉ P)
                        ∗ (⤉ Duty(tid) ((κu, 0, ▿ γκu tt) :: ds))
                        ∗ ◇[κu](ℓu, μu)
                  )%S, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST".
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as) in "PRE"; simpl.
    iDestruct "PRE" as "(#MEM & #SPIN & PCs & DUTY & PCS & PCS')".
    iPoseProof (isSpinlock_unfold with "SPIN") as "[#OBL #INV]". iClear "SPIN".
    unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iMod (ccs_make_fine with "[OBL PCS]") as "CCS". iSplitR. done. instantiate (1:=1). done.
    iRevert "PCS' PCs DUTY POST". iMod (ccs_ind2 with "[CCS] []") as "IH". done. 2: iApply "IH".
    iModIntro. iExists 0. iIntros "IH". iModIntro. iIntros "PCS PCs DUTY POST".
    (* Yield *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR2 with "[DUTY PCS]"). auto. auto. iFrame.
    iIntros "DUTY CRED _". rred2r.
    (* Open invariant *)
    iInv "INV" as "SI" "SI_CLOSE".
    iEval (unfold spinlockInv; simpl; red_tl_all) in "SI".
    iDestruct "SI" as (γs) "SI". iEval (red_tl) in "SI".
    iDestruct "SI" as (κu) "SI". iEval (red_tl_all; simpl) in "SI".
    iDestruct "SI" as "(LB & [(PTX & LW & P) | (PTX & LIVE & #PRM & #LINK)])".
    { (* Success *)
      iApply (SCMem_cas_fun_spec with "[PTX] [-]"). auto. set_solver. iFrame.
      { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%u [%H' PTX]]". des_ifs. des; clarify. rred2r. iApply wpsim_tauR. rred2r.
      (* Allocate unlocking obligation *)
      iMod OneShots.alloc as "[%γs' LIVE]".
      iMod (alloc_obligation_fine ℓu (1 + μu)) as "(%κu' & #OBL' & PC & PENDING)".
      iPoseProof (pc_split _  _ 1 with "PC") as "[PC' PC]".
      iAssert (#=> ◇[κu'](1, 1))%I with "[PC']" as "> PC'".
      { destruct (Nat.eq_dec ℓu 1). subst; done.
        iMod (pc_drop _ 1 _ _ 1 1 with "[PC']") as "PC'". auto. done. done.
      }
      iEval (rewrite <- Qp.half_half) in "PENDING".
      iPoseProof (pending_split with "PENDING") as "[PENDING PENDING']".
      iMod (duty_add with "[DUTY PC' PENDING] []") as "DUTY". iFrame.
      { instantiate (1:= (▿ γs' tt)%S). simpl. iModIntro. red_tl_all. iIntros "#H". iModIntro. done. }
      iPoseProof (duty_delayed_tpromise with "DUTY") as "#DPRM". simpl; left; auto.
      iMod (activate_tpromise with "DPRM PENDING'") as "[#PRM _]". iClear "DPRM".
      iMod (AuthExcls.b_w_update _ _ _ (γs', κu') with "LB LW") as "[LB LW]".
      iMod (link_new_fine _ _ _ _ 0 with "[PCs]") as "#LINK".
      { iSplitR; cycle 1. iApply "PCs". done. }
      (* Close the invariant *)
      iMod ("SI_CLOSE" with "[PTX LIVE LB]") as "_".
      { iEval (simpl; unfold spinlockInv; red_tl_all). iExists γs'. red_tl. iExists κu'. red_tl_all.
        iFrame. iRight; iFrame. iSplit; auto.
      }
      iApply ("POST" with "[-]").
      { do 2 (red_tl; iExists _); red_tl_all; iFrame. }
    }
    { (* Failure *)
      iApply (SCMem_cas_fun_spec with "[PTX] [-]"). auto. set_solver. iFrame.
      { simpl. iApply (tgt_interp_as_equiv with "MEM"). iIntros. iSplit.
        { iIntros. simpl. red_tl; simpl. iSplit; [done | iPureIntro; auto]. }
        { simpl. red_tl; simpl. iIntros "[? _]". done. }
      }
      iIntros (rv) "[%u [%H' PTX]]". des_ifs. des; clarify. rred2r. iApply wpsim_tauR. rred2r. iApply wpsim_tauR.
      iMod (tpromise_progress with "[PRM CRED]") as "[PC | #SHOT]". iFrame. done.
      2:{ iExFalso. iEval (simpl; red_tl_all) in "SHOT". iApply (OneShots.pending_not_shot with "LIVE SHOT"). }
      iMod (link_amplify with "[LINK PC]") as "PC". iFrame. done. simpl.
      iMod ("IH" with "PC") as "IH".
      (* Close the invariant *)
      iMod ("SI_CLOSE" with "[PTX LIVE LB]") as "_".
      { iEval (simpl; unfold spinlockInv; red_tl_all). iExists γs. red_tl. iExists κu. red_tl_all.
        iFrame. iRight; iFrame. iSplit; auto.
      }
      iApply wpsim_stutter_mon. instantiate (1:=ps); auto. instantiate (1:=pt); auto.
      iApply ("IH" with "PCs DUTY POST").
    }
  Unshelve. lia.
  Qed.

  Lemma Spinlock_unlock_spec
        tid n
    :
    ⊢ ∀ κs x γl (P : sProp n) ℓL μn (ds : list (nat * nat * sProp n)) γκu κu,
        [@ tid, n, ⊤ @]
          ⧼⟦((syn_tgt_interp_as n sndl (fun m => (s_memory_black m)))
               ∗ (⤉ isSpinlock n κs x γl P ℓL μn)
               ∗ (⤉ ○ γl (γκu, κu))
               ∗ (⤉ P)
               ∗ (⤉ Duty(tid) ((κu, 0, ▿ γκu tt) :: ds))
               ∗ ◇{((κu, 0, ▿ κu tt) :: ds)@1}(1, 1)
            )%S, 1+n⟧⧽
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.unlock x))
            ⧼rv, ⟦((⤉ Duty(tid) ds))%S, 1+n⟧⧽
  .
  Proof.
    iIntros (? ? ? ? ? ? ? ? ?).
    iStartTriple. iIntros "PRE POST".
    (* Preprocess. *)
    iEval (red_tl_all; rewrite red_syn_tgt_interp_as) in "PRE"; simpl.
    iDestruct "PRE" as "(#MEM & #SPIN & LW & P & DUTY & PCS)".
    iPoseProof (isSpinlock_unfold with "SPIN") as "[#OBL #INV]". iClear "SPIN".
    unfold Spinlock.unlock.
    (* Yield *)
    rred2r. iApply (wpsim_yieldR with "[DUTY PCS]"). auto. iFrame. done.
    iIntros "DUTY _". rred2r.
    (* Open invariant *)
    iInv "INV" as "SI" "SI_CLOSE".
    iEval (unfold spinlockInv; simpl; red_tl_all) in "SI".
    iDestruct "SI" as (γs') "SI". iEval (red_tl) in "SI".
    iDestruct "SI" as (κu') "SI". iEval (red_tl_all; simpl) in "SI".
    iDestruct "SI" as "(LB & [(PTX & LW' & _) | (PTX & LIVE & #PRM & #LINK)])".
    { iExFalso. iApply (AuthExcls.w_w_false with "LW LW'"). }
    iPoseProof (AuthExcls.b_w_eq with "LB LW") as "%EQ"; clarify.
    (* Store *)
    iApply (SCMem_store_fun_spec with "[PTX] [-]"). auto. set_solver.
    { iFrame. done. }
    iIntros (rv) "PTX". rred2r. iApply wpsim_tauR. rred2r.
    (* Close invariant *)
    iPoseProof (unfold_tpromise with "PRM") as "[_ #AO]".
    iMod (OneShots.pending_shot _ tt with "LIVE") as "#SHOT".
    iMod (duty_fulfill with "[DUTY]") as "DUTY".
    { iFrame. simpl; red_tl_all. iSplit; done. }
    iMod ("SI_CLOSE" with "[PTX LB LW P]") as "_".
    { iEval (simpl; unfold spinlockInv; red_tl_all). do 2 (iExists _; red_tl_all). iFrame. iLeft; iFrame. }
    iApply "POST". red_tl. done.
  Qed.

End SPEC.
Global Opaque Spinlock.lock Spinlock.unlock.
