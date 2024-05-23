From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import PCM IProp IPM.
From Fairness Require Import IndexedInvariants OpticsInterp SimWeakest.
From Fairness Require Import TemporalLogic TemporalLogicFull SCMemSpec.
(* From Fairness Require Import ModSim. *)
(* Import NatStructs. *)

Module Spinlock.

  Section SPINLOCK.

    Variable Client : Mod.t.
    (* Variable gvs : list nat. *)
    Notation state := (Mod.state Client).
    Notation ident := (Mod.ident Client).
    (* Notation state := (OMod.closed_state Client (SCMem.mod gvs)). *)
    (* Notation ident := (OMod.closed_ident Client (SCMem.mod gvs)). *)

    Notation unlocked := (SCMem.val_nat 0).
    Notation locked := (SCMem.val_nat 1).

    Definition lock :
      (* ktree (threadE void unit) SCMem.val unit *)
      ktree (threadE ident state) SCMem.val unit
      :=
      fun x =>
        ITree.iter
          (fun (_ : unit) =>
             b <- (OMod.call "cas" (x, unlocked, locked));;
             if (b : bool) then Ret (inr tt) else Ret (inl tt)) tt.

    Definition unlock :
      (* ktree (threadE void unit) SCMem.val unit *)
      ktree (threadE ident state) SCMem.val unit
      :=
      fun x => (OMod.call "store" (x, unlocked)).

    (** TODO : more rules for module composition. *)
    (* Definition omod : Mod.t := *)
    (*   Mod.mk *)
    (*     (* tt *) *)
    (*     (Mod.st_init Client) *)
    (*     (Mod.get_funs [("lock", Mod.wrap_fun lock); *)
    (*                    ("unlock", Mod.wrap_fun unlock)]) *)
    (* . *)

    (* Definition module gvs : Mod.t := *)
    (*   OMod.close *)
    (*     (omod) *)
    (*     (SCMem.mod gvs) *)
    (* . *)

  End SPINLOCK.

End Spinlock.

Section SIM.

  Variable src_state : Type.
  Variable src_ident : Type.
  Variable Client : Mod.t.
  Variable gvs : list nat.
  Notation tgt_state := (OMod.closed_state Client (SCMem.mod gvs)).
  Notation tgt_ident := (OMod.closed_ident Client (SCMem.mod gvs)).

  (* Context {STT : StateTypes}. *)
  Local Instance STT : StateTypes := Build_StateTypes src_state tgt_state src_ident tgt_ident.
  Notation Formula := (@Formula XAtom STT).

  Context `{Σ : GRA.t}.
  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Formula) Σ}.
  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA st_src_type) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA st_tgt_type) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA id_src_type) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA id_tgt_type) Σ}.
  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA id_tgt_type Formula) Σ}.
  (* SCMem related RAs *)
  Context `{MEMRA: @GRA.inG memRA Σ}.
  (* Map from nat to Excl unit RA. *)
  Context `{EXCLUNITS: @GRA.inG ExclUnitsRA Σ}.
  (* Auth agree Qp RA. *)
  Context `{AAGREE_QP: @GRA.inG (AuthAgreeRA Qp) Σ}.


  (** Invariants. *)
  Definition spinlockInv (n : nat) (r : nat) (x : SCMem.val) (P : Formula n) (k l : nat) : Formula n :=
    ((∃ (q : τ{Qp}),
         (➢(agree_b_Qp q))
           ∗
           (((x ↦ 0) ∗ (◇(k @ l) 1) ∗ (➢(excls r)) ∗ (➢(agree_w_Qp q)) ∗ P)
            ∨ ((x ↦ 1) ∗ live(k, q) ∗ ∃ (u : τ{nat}), live(u, 1/2) ∗ (-(u @ l)-◇ emp) ∗ (u -( 0 )-◇ k))))
     ∨ dead(k)
    )%F.

  Definition isSpinlock n (E : coPset) (r : nat) (x : SCMem.val) (P : Formula n) (k l : nat) : Formula n :=
    (∃ (N : τ{namespace}) (o : τ{Ord.t}),
        ⌜(↑N ⊆ E)⌝ ∗ ◆(k @ l | o) ∗ syn_inv _ N (spinlockInv n r x P k l))%F.


  Lemma spinlock_lock_spec
        n
        tid R_src R_tgt (Q : R_src -> R_tgt -> iProp) R G ps pt itr_src ktr_tgt
        (Es : coPsets) E
        (MASK_TOP : OwnEs_top Es)
        (MASK_STTGT : mask_has_st_tgt Es n)
    (* (MASK : match Es !! n with Some E' => E ⊆ E' | None => True end) *)
    :
    ⊢
      (∀ r x (P : Formula n) k l q (ds : list (nat * nat * Formula n)),
          (⟦((syn_tgt_interp_as n sndl (fun m => (➢ (scm_memory_black m))))
               ∗ ⤉((isSpinlock n E r x P k l)
                     ∗ live(k, q) ∗ Duty(tid) ds ∗ ◇[List.map fst ds @ l](2)))%F, S n⟧)
            -∗
            (∀ (rv : _),
                (⟦(∃ (u : τ{nat}), (➢(excls r)) ∗ P ∗ (➢(agree_w_Qp q)) ∗ Duty(tid) ((u, l, emp) :: ds) ∗ ◇(u @ l) 1)%F , n⟧)
                  -∗
                  (wpsim (S n) tid ∅ R G Q ps true (trigger Yield;;; itr_src)
                         (ktr_tgt rv)))
            -∗
            wpsim (S n) tid Es R G Q ps pt (trigger Yield;;; itr_src)
            (OMod.close_itree Client (SCMem.mod gvs) (Spinlock.lock Client x) >>= ktr_tgt))
  .
  Proof.
    iIntros (? ? ? ? ? ? ?) "PRE POST".
    unfold Spinlock.lock.
    (* Preprocess for induction. *)
    iApply wpsim_free_all. auto.
    unfold isSpinlock. ss.
    iEval red_tl in "PRE". ss. iEval (rewrite red_syn_tgt_interp_as) in "PRE".
    iDestruct "PRE" as "(#STINTP & (%N & SL) & LIVE & DUTY & PCS)".
    iEval red_tl in "SL". ss. iDestruct "SL" as "[%o SL]".
    iEval red_tl in "SL". ss. iDestruct "SL" as "(%IN & #LO & INV)".
    rewrite red_syn_inv. iPoseProof "INV" as "#INV".
    iMod ((pcs_decr _ _ 1 1 2) with "PCS") as "[PCS PCS2]". ss.
    iMod (ccs_make k l o _ 0 with "[PCS2]") as "CCS". iFrame. auto.
    iMod (pcs_drop _ _ _ _ 0 with "PCS") as "PCS". lia.
    (* Set up induction hypothesis. *)
    iRevert "LIVE DUTY PCS POST". iMod (ccs_ind with "CCS []") as "IND".
    2:{ iApply "IND". }
    iModIntro. iExists l, 1. iIntros "IH". iModIntro. iIntros "LIVE DUTY PCS POST".
    (* Start an iteration. *)
    iEval (rewrite unfold_iter_eq). rred2r.
    iApply (wpsim_yieldR with "[DUTY PCS]"). 2: iFrame. auto. Unshelve. 2: auto.
    iIntros "DUTY FC". iModIntro. rred2r.
    TODO

    iApply cas_fun_spec.


    iInv "STINTP" as (st) "ST" "ST_CLOSE".
    iDestruct "ST" as "(%mem & VWM & MBLACK)". iEval (simpl; red_sem; simpl) in "MBLACK".
    iApply wpsim_getR. iSplit. iFrame. rred2r.
    iEval (unfold OMod.emb_callee).
    
    

    TODO
      map_event (OMod.emb_callee Client (SCMem.mod gvs))
        (Mod.wrap_fun SCMem.cas_fun (Any.upcast (x, 0, 1)));; (tau;; unwrap (Any.downcast rv)));;
  Variable p_mem : Prism.t id_tgt_type SCMem.val.
  Variable l_mem : Lens.t st_tgt_type SCMem.t.
  Let emb_mem := plmap p_mem l_mem.

    rewrite @close_itree_trigger_call.
    

    TODO
  Lemma wpsim_yieldR
        y (LT: y < x)
        E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
        (l : list (nat * nat * Vars y))
    :
    ((Duty(tid) l) ∗ ◇[List.map fst l @ 0](1))
      -∗
      ((Duty(tid) l)
         -∗
         €
         -∗
         (=|x|=(fairI (ident_tgt:=ident_tgt) x)={E, ∅}=>
            (wpsim ∅ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
    




collection_credits_decr:
  ∀ {Σ : GRA.t} {OBLGRA : GRA.inG ObligationRA.t Σ} (k : nat) (o : Ord.t) (ps : list (nat * nat)) (l m a : nat),
    0 < a → (◆[ k & ps @ l | o]) ∗ (◇( k @ m) a) -∗ #=> (∃ o' : Ord.t, (◆[ k & ps @ l | o']) ∗ ⌜(o' < o)%ord⌝ ∗ (◇[ ps @ l] 1))
cc_ind:
  ∀ {Σ : GRA.t} {OBLGRA : GRA.inG ObligationRA.t Σ} (k : nat) (o : Ord.t) (ps : list (nat * nat)) (l : nat) (P : iProp),
    ◆[ k & ps @ l | o] -∗ □ (∃ m a : nat, (⌜0 < a⌝ -∗ ◇( k @ m) a ==∗ (◇[ ps @ l] 1) ∗ P) ==∗ P) ==∗ P


  Lemma AbsLock_unlock
        R_src R_tgt tid
        (src: thread void (sE unit) R_src)
        tgt
        r g
        (Q: R_src -> R_tgt -> iProp)
        l
    :
    ((inv N_lock lock_will_unlock)
       ∗
       (OwnM (Excl.just tt: Excl.t unit))
       ∗
       (∃ k, (ObligationRA.duty inlp tid ((k, Ord.S Ord.O) :: l))
               ∗ (OwnM (Auth.white (Excl.just k: Excl.t nat)))
               ∗ (ObligationRA.taxes ((k, Ord.S Ord.O) :: l) 3%ord))
    )
      ∗
      ((ObligationRA.duty inlp tid l)
         -∗
         (stsim tid ⊤ r g Q
                false false
                (trigger Yield;;; src)
                (tgt)))
      ⊢
      (stsim tid ⊤ r g Q
             false false
             (trigger Yield;;; src)
             (OMod.close_itree ClientImpl.omod (ModAdd (SCMem.mod gvs) AbsLock.mod) (R:=unit) (OMod.call "unlock" ());;; tgt)).
  Proof.
    iIntros "[[# LOCK_INV [EXCL [% [DUTY [LOCK TAXES]]]]] SIM]".
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX]".
    { instantiate (1:= 2%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_ord_split_one with "TAXES") as "> [TAXES TAX1]".
    { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
    iPoseProof (ObligationRA.taxes_single_is_tax with "TAXES") as "TAX2".
    rewrite close_itree_call. ss. unfold OMod.emb_callee, emb_r. rewrite <- map_event_compose. rewrite <- plmap_compose. rred.
    iApply (stsim_yieldR with "[DUTY TAX]"). ss. iFrame.
    iIntros "DUTY _". rred.
    unfold AbsLock.unlock_fun, Mod.wrap_fun. rred.
    iApply (stsim_yieldR with "[DUTY TAX1]"). ss. iFrame.
    iIntros "DUTY _". rred.
    iInv "LOCK_INV" as "I1" "K1". do 4 (iDestruct "I1" as "[% I1]").
    iDestruct "I1" as "[B1 [B2 [MEM [STGT [BLKS [SUM [CONTRA | CASE]]]]]]]".
    { iDestruct "CONTRA" as "[_ [_ EXCL2]]". iPoseProof (OwnM_valid with "[EXCL EXCL2]") as "%".
      { instantiate (1:= (Excl.just (): Excl.t unit) ⋅ (Excl.just (): Excl.t unit)).
        iSplitL "EXCL". all: iFrame. }
      eapply Excl.wf in H. inversion H.
    }
    iDestruct "CASE" as "[% [JPEND [JBLK [JCOR AMPs]]]]". subst own.
    iApply stsim_getR. iSplit. iFrame. rred.
    iApply (stsim_modifyR with "STGT"). iIntros "STGT". rred.
    iPoseProof (black_white_equal with "B2 LOCK") as "%". subst.
    iMod ("K1" with "[EXCL LOCK B1 B2 MEM BLKS SUM STGT]") as "_".
    { unfold lock_will_unlock. iExists false, mem, wobl, k. iFrame.
      iLeft. iFrame. auto.
    }
    iPoseProof (ObligationRA.pending_shot with "JPEND") as "> SHOT".
    iPoseProof (ObligationRA.duty_done with "DUTY SHOT") as "> DUTY".
    iApply (stsim_yieldR with "[DUTY TAX2]"). ss.
    { iSplitL "DUTY". iFrame.
      iPoseProof (ObligationRA.tax_cons_unfold with "TAX2") as "[_ TAX2]". iFrame.
    }
    iIntros "DUTY _". rred.
    iApply stsim_tauR. rred.
    iApply stsim_reset. iApply "SIM". iFrame.
  Qed.

  (* Lemma spinlock_lock_spec2 *)
  (*       n *)
  (*       tid R_src R_tgt (Q : R_src -> R_tgt -> iProp) R G ps pt itr_src ktr_tgt *)
  (*       (* (TOP : OwnEs_top Es) *) *)
  (*       (Es : coPsets) E *)
  (*       (MASK : match Es !! n with Some E' => E ⊆ E' | None => True end) *)
  (*   : *)
  (*   ⊢ *)
  (*   (∀ r x (P : Formula n) k l q (ds : list (nat * nat * Formula n)), *)
  (*       (Duty(tid) ds =|S n|={Es, ∅}=∗ emp%I) *)
  (*       → *)
  (*         (⟦((isSpinlock n E r x P k l) ∗ live(k, q) ∗ Duty(tid) ds ∗ ◇[List.map fst ds @ l](2))%F, n⟧) *)
  (*           -∗ *)
  (*           ((⟦(∃ (u : τ{nat}), (➢(excls r)) ∗ (➢(agree_w_Qp q)) ∗ P ∗ Duty(tid) ((u, l, emp) :: ds) ∗ ◇(u @ l) 1)%F , n⟧) *)
  (*              -∗ *)
  (*              (wpsim (S n) tid ∅ R G Q ps true itr_src (ktr_tgt tt))) *)
  (*           -∗ *)
  (*           wpsim (S n) tid Es R G Q ps pt itr_src *)
  (*           (map_event emb_spinlock (Spinlock.lock x) >>= ktr_tgt)). *)
  (* Proof. *)
  (*   iIntros (? ? ? ? ? ? ?) "CLOSE PRE POST". *)


End SIM.
