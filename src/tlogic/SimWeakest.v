From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib ModSim ModSimNat.
From Fairness Require PCMLarge.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import ISim.

From stdpp Require Import coPset gmap namespaces.
From Fairness Require Export IndexedInvariants NatMapRALarge MonotoneRA FairnessRA ObligationRA SimDefaultRA OpticsInterp.
From Fairness Require Export FairBeh.
Require Import Coq.Sorting.Mergesort.

Require Import Program.

Set Implicit Arguments.

Section STATE.

  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Let srcE := threadE ident_src state_src.
  Let tgtE := threadE ident_tgt state_tgt.

  Let shared_rel := TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp.

  Local Notation index := nat.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.

  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.

  (* State related default RAs *)
  (* Context `{MONORA: @GRA.inG monoRA Σ}. *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.

  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.

  Variable x : index.

  Let rel := (forall R_src R_tgt (Q: R_src -> R_tgt -> iProp), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> iProp).

  Variable tid: thread_id.

  Let unlift_rel
      (r: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel): rel :=
        fun R_src R_tgt Q ps pt itr_src itr_tgt =>
          (∀ ths im_src im_tgt st_src st_tgt,
              (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅))
                -∗
                (@r R_src R_tgt (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)) ∗ Q r_src r_tgt) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt))%I.

  Let lift_rel (rr: rel):
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
        fun R_src R_tgt QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt =>
          (∃ (Q: R_src -> R_tgt -> iProp)
             (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                          (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)) ∗ Q r_src r_tgt)),
              rr R_src R_tgt Q ps pt itr_src itr_tgt ∗
                 (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)))%I.

  Let unlift_rel_base r
    :
    forall R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (r R_src R_tgt Q ps pt itr_src itr_tgt)
        -∗
        (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅))
        -∗
        (lift_rel
           r
           (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)) ∗ Q r_src r_tgt)
           ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel. i.
    iIntros "H D". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let unlift_lift r
    :
    forall R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (lift_rel (unlift_rel r) Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        ⊢ (r R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel, unlift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iApply ("H" with "D").
  Qed.

  Let lift_unlift (r0: rel) (r1: forall R_src R_tgt (Q: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel)
    :
    (* bi_entails *)
    (∀ R_src R_tgt (Q: R_src -> R_tgt -> shared_rel) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
        @lift_rel r0 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt
                  -∗ r1 R_src R_tgt Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      ⊢
      (∀ R_src R_tgt Q ps pt itr_src itr_tgt,
          r0 R_src R_tgt Q ps pt itr_src itr_tgt -∗ unlift_rel r1 Q ps pt itr_src itr_tgt).
  Proof.
    unfold lift_rel, unlift_rel.
    iIntros "IMPL" (? ? ? ? ? ? ?) "H". iIntros (? ? ? ? ?) "D".
    iApply "IMPL". iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let lift_rel_mon (rr0 rr1: rel)
      (MON: forall R_src R_tgt Q ps pt itr_src itr_tgt,
          (* bi_entails *)
          (rr0 R_src R_tgt Q ps pt itr_src itr_tgt)
            ⊢
            (#=> rr1 R_src R_tgt Q ps pt itr_src itr_tgt))
    :
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel) ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt,
      (* bi_entails *)
      (lift_rel rr0 QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
        ⊢
        (#=> lift_rel rr1 QQ ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt).
  Proof.
    unfold lift_rel. i.
    iIntros "[% [% [H D]]]". subst.
    iPoseProof (MON with "H") as "> H".
    iModIntro. iExists _, _. Unshelve.
    { iFrame. }
    { auto. }
  Qed.

  Let I: shared_rel :=
        fun ths im_src im_tgt st_src st_tgt =>
          (default_I x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅))%I.

  Definition wpsim (Es : coPsets) : rel -> rel -> rel :=
    fun r g
      R_src R_tgt Q ps pt itr_src itr_tgt =>
      (∀ ths im_src im_tgt st_src st_tgt,
          (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs Es))
            -∗
            (isim
               tid
               I
               (lift_rel r)
               (lift_rel g)
               (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid x ths im_src im_tgt st_src st_tgt ∗ (wsat_auth x ∗ wsats x ∗ OwnEs ∅)) ∗ Q r_src r_tgt)
               ps pt itr_src itr_tgt
               ths im_src im_tgt st_src st_tgt))%I
  .

  Record mytype
         (A: Type) :=
    mk_mytype {
        comp_a: A;
        comp_ths: TIdSet.t;
        comp_im_src: imap ident_src owf;
        comp_im_tgt: imap (sum_tid ident_tgt) nat_wf;
        comp_st_src: state_src;
        comp_st_tgt: state_tgt;
      }.

  (* Lemmas for wpsim. *)

  Lemma wpsim_upd Es r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (#=> (wpsim Es r g Q ps pt itr_src itr_tgt))
      -∗
      (wpsim Es r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D". iMod "H".
    iApply "H". auto.
  Qed.

  Lemma wpsim_discard Es n E1 E0 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (TOP: E0 ⊆ E1)
    :
    (wpsim (<[n:=E0]>Es) r g Q ps pt itr_src itr_tgt)
      -∗
      (wpsim (<[n:=E1]>Es) r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "(D & WA & WS & E)".
    iApply "H". iFrame. iApply (OwnEs_update_one with "E").
    iIntros "E". iPoseProof (OwnE_subset with "E") as "[E0 _]"; [eapply TOP|].
    iFrame.
  Qed.

  Lemma wpsim_free_all Es r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (TOP: OwnEs_top Es)
    :
    (wpsim ∅ r g Q ps pt itr_src itr_tgt)
      -∗
      (wpsim Es r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "(D & WA & WS & E)".
    iMod (OwnEs_free_all with "E") as "E". auto.
    iApply "H". iFrame.
  Qed.

  Lemma wpsim_base Es r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (TOP: OwnEs_top Es)
        (* (TOP: ⊤ ⊆ E) *)
    :
    (@r _ _ Q ps pt itr_src itr_tgt)
      -∗
      (wpsim Es r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    rewrite <- wpsim_free_all; [|eassumption].
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_base.
    iApply (unlift_rel_base with "H D").
  Qed.

  TODO

  Lemma wpsim_mono_knowledge E (r0 g0 r1 g1: rel) R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (MON0: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                      ps pt itr_src itr_tgt,
            (@r0 _ _ Q ps pt itr_src itr_tgt)
              -∗
              (#=> (@r1 _ _ Q ps pt itr_src itr_tgt)))
        (MON1: forall R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                      ps pt itr_src itr_tgt,
            (@g0 _ _ Q ps pt itr_src itr_tgt)
              -∗
              (#=> (@g1 _ _ Q ps pt itr_src itr_tgt)))
    :
    bi_entails
      (wpsim E r0 g0 Q ps pt itr_src itr_tgt)
      (wpsim E r1 g1 Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_mono_knowledge.
    { eapply lift_rel_mon. eauto. }
    { eapply lift_rel_mon. eauto. }
    iApply ("H" with "D").
  Qed.

  Lemma wpsim_coind E A
        (R_src: forall (a: A), Type)
        (R_tgt: forall (a: A), Type)
        (Q: forall (a: A), R_src a -> R_tgt a -> iProp)
        (ps pt: forall (a: A), bool)
        (itr_src : forall (a: A), itree srcE (R_src a))
        (itr_tgt : forall (a: A), itree tgtE (R_tgt a))
        (P: forall (a: A), iProp)
        (r g0: rel)
        (TOP: ⊤ ⊆ E)
        (COIND: forall (g1: rel) a,
            (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -* @g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 **
                 (∀ a, P a -* @g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))
              -∗
              (P a)
              -∗
              (wpsim ⊤ r g1 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a)))
    :
    (forall a, bi_entails (P a) (wpsim E r g0 (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))).
  Proof.
    cut (forall (m: mytype A),
            bi_entails
              ((fun m => P m.(comp_a) ** (default_I_past tid m.(comp_ths) m.(comp_im_src) m.(comp_im_tgt) m.(comp_st_src) m.(comp_st_tgt) ** (wsat ** OwnE ⊤))) m)
              (isim tid I (lift_rel r) (lift_rel g0) ((fun m => fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** Q m.(comp_a) r_src r_tgt) m)
                    ((fun m => ps m.(comp_a)) m) ((fun m => pt m.(comp_a)) m) ((fun m => itr_src m.(comp_a)) m) ((fun m => itr_tgt m.(comp_a)) m) (comp_ths m) (comp_im_src m) (comp_im_tgt m) (comp_st_src m) (comp_st_tgt m))).
    { ss. i. rewrite <- wpsim_discard; [|eassumption].
      unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
      specialize (H (mk_mytype a ths im_src im_tgt st_src st_tgt)). ss.
      iApply H. iFrame.
    }
    eapply isim_coind. i. iIntros "[# CIH [H D]]".
    unfold wpsim in COIND.
    iAssert (□((∀ R_src R_tgt (Q: R_src -> R_tgt -> iProp)
                  ps pt itr_src itr_tgt,
                   @g0 R_src R_tgt Q ps pt itr_src itr_tgt -* @unlift_rel g1 R_src R_tgt Q ps pt itr_src itr_tgt)
                 **
                 (∀ a, P a -* @unlift_rel g1 (R_src a) (R_tgt a) (Q a) (ps a) (pt a) (itr_src a) (itr_tgt a))))%I with "[CIH]" as "CIH'".
    { iPoseProof "CIH" as "# [CIH0 CIH1]". iModIntro. iSplitL.
      { iApply (lift_unlift with "CIH0"). }
      { iIntros. unfold unlift_rel. iIntros.
        iSpecialize ("CIH1" $! (mk_mytype _ _ _ _ _ _)). ss.
        iApply "CIH1". iFrame.
      }
    }
    iPoseProof (COIND with "CIH' H D") as "H".
    iApply (isim_mono_knowledge with "H").
    { auto. }
    { i. iIntros "H". iModIntro. iApply unlift_lift. auto. }
  Qed.

  Global Instance wpsim_elim_upd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=> P) P (wpsim E r g Q ps pt itr_src itr_tgt) (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    typeclasses eauto.
  Qed.

  Lemma wpsim_FUpd E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (FUpd (fairI (ident_tgt:=ident_tgt)) E0 E1 (wpsim E1 r g Q ps pt itr_src itr_tgt))
      -∗
      (wpsim E0 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    Local Transparent FUpd.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "[[% [% [[D X0] X1]]] (WSAT & E)]".
    iAssert (fairI (ident_tgt:=ident_tgt) ** (wsat ** OwnE E0)) with "[X0 X1 WSAT E]" as "C".
    { iFrame. }
    unfold FUpd.
    iMod ("H" with "C") as "(F & WSAT & E & H)".
    iApply "H". iFrame. iExists _. iFrame. auto.
  Qed.

  Lemma wpsim_FUpd_weaken E0 E1 r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
        (SUB: E0 ⊆ E1)
    :
    (FUpd (fairI (ident_tgt:=ident_tgt)) E0 E0 (wpsim E1 r g Q ps pt itr_src itr_tgt))
      -∗
      (wpsim E1 r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply wpsim_FUpd. iApply FUpd_mask_mono; eauto.
  Qed.

  Global Instance wpsim_elim_FUpd_gen
         E0 E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (E0 ⊆ E2) p false (FUpd (fairI (ident_tgt:=ident_tgt)) E0 E1 P) P (wpsim E2 r g Q ps pt itr_src itr_tgt) (wpsim (E1 ∪ (E2 ∖ E0)) r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (FUpd_mask_frame _ _ _ (E2 ∖ E0) with "H0") as "H0".
    { eapply disjoint_difference_r1. set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2.
    2: { eapply leibniz_equiv. eapply union_difference. ss. }
    iApply wpsim_FUpd. iMod "H0". iModIntro. iApply "H1". iFrame.
  Qed.

  Global Instance wpsim_elim_FUpd_eq
         E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal (E1 ⊆ E2) p false (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E1 P) P (wpsim E2 r g Q ps pt itr_src itr_tgt) (wpsim E2 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wpsim_FUpd_weaken.
    { eauto. }
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_elim_FUpd
         E1 E2 r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 P) P (wpsim E1 r g Q ps pt itr_src itr_tgt) (wpsim E2 r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wpsim_FUpd. iMod "H0".
    iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_add_modal_FUpd
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt
         P
    :
    AddModal (FUpd (fairI (ident_tgt:=ident_tgt)) E E P) P (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]". iApply ("H1" with "H0").
  Qed.

  Global Instance wpsim_elim_iupd_edge
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=(ObligationRA.edges_sat)=> P) P (wpsim E r g Q ps pt itr_src itr_tgt) (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]" (? ? ? ? ?) "[[% [% D]] [C E]]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]"; auto.
    { iApply edges_sat_sub. }
    iApply ("H1" with "P"). iFrame. iExists _. eauto.
  Qed.

  Global Instance wpsim_elim_iupd_arrow
         E r g R_src R_tgt
         (Q: R_src -> R_tgt -> iProp)
         ps pt itr_src itr_tgt p
         P
    :
    ElimModal True p false (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt))=> P) P (wpsim E r g Q ps pt itr_src itr_tgt) (wpsim E r g Q ps pt itr_src itr_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]" (? ? ? ? ?) "[[% [% D]] [C E]]".
    iPoseProof (IUpd_sub_mon with "[] H0 D") as "> [D P]"; auto.
    { iApply arrows_sat_sub. }
    iApply ("H1" with "P"). iFrame. iExists _. eauto.
  Qed.

  (* Global Instance mupd_elim_iupd_edge *)
  (*        P Q E1 E2 p Inv *)
  (*   : *)
  (*   ElimModal True p false (#=(ObligationRA.edges_sat)=> P) P (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q). *)
  (* Proof. *)
  (*   unfold ElimModal. rewrite bi.intuitionistically_if_elim. *)
  (*   i. iIntros "[H0 H1]". *)
  (*   iPoseProof (IUpd_sub_mon with "[] H0") as "H0". *)
  (*   { iApply SubIProp_sep_l. } *)
  (*   iMod "H0". iApply ("H1" with "H0"). *)
  (* Qed. *)

  (* Global Instance mupd_elim_upd_arrow *)
  (*        P Q E1 E2 p Inv *)
  (*   : *)
  (*   ElimModal True p false (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt))=> P) P (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (MUpd Inv (fairI (ident_tgt:=ident_tgt)) E1 E2 Q). *)
  (* Proof. *)
  (*   unfold ElimModal. rewrite bi.intuitionistically_if_elim. *)
  (*   i. iIntros "[H0 H1]". *)
  (*   iPoseProof (IUpd_sub_mon with "[] H0") as "H0". *)
  (*   { iApply SubIProp_sep_r. } *)
  (*   iMod "H0". iApply ("H1" with "H0"). *)
  (* Qed. *)

  Global Instance mupd_elim_fupd_edge
         P Q E1 E2 p
    :
    ElimModal True p false (#=(ObligationRA.edges_sat)=> P) P (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_l. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Global Instance mupd_elim_fupd_arrow
         P Q E1 E2 p
    :
    ElimModal True p false (#=(ObligationRA.arrows_sat (S:=sum_tid ident_tgt))=> P) P (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q) (FUpd (fairI (ident_tgt:=ident_tgt)) E1 E2 Q).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iPoseProof (IUpd_sub_mon with "[] H0") as "H0".
    { iApply SubIProp_sep_r. }
    iMod "H0". iApply ("H1" with "H0").
  Qed.

  Lemma wpsim_wand E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q0 ps pt itr_src itr_tgt)
      -∗
      (∀ r_src r_tgt,
          ((Q0 r_src r_tgt) -∗ #=> (Q1 r_src r_tgt)))
      -∗
      (wpsim E r g Q1 ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H0 H1" (? ? ? ? ?) "D".
    iApply isim_wand.
    iPoseProof ("H0" $! _ _ _ _ _ with "D") as "H0".
    iSplitR "H0"; [|auto]. iIntros (? ? ? ? ? ? ?) "[D H0]".
    iPoseProof ("H1" $! _ _ with "H0") as "> H0". iModIntro. iFrame.
  Qed.

  Lemma wpsim_mono E r g R_src R_tgt
        (Q0 Q1: R_src -> R_tgt -> iProp)
        (MONO: forall r_src r_tgt,
            (Q0 r_src r_tgt)
              -∗
              (#=> (Q1 r_src r_tgt)))
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q0 ps pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q1 ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H". iApply (wpsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma wpsim_frame E r g R_src R_tgt
        P (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q ps pt itr_src itr_tgt)
      -∗
      P
      -∗
      (wpsim E r g (fun r_src r_tgt => P ** Q r_src r_tgt) ps pt itr_src itr_tgt)
  .
  Proof.
    iIntros "H0 H1". iApply (wpsim_wand with "H0").
    iIntros. iModIntro. iFrame.
  Qed.

  Lemma wpsim_bind_top E r g R_src R_tgt S_src S_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt (itr_src: itree srcE S_src) (itr_tgt: itree tgtE S_tgt)
        ktr_src ktr_tgt
    :
    (wpsim E r g (fun s_src s_tgt => wpsim ⊤ r g Q false false (ktr_src s_src) (ktr_tgt s_tgt)) ps pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt (itr_src >>= ktr_src) (itr_tgt >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_bind. iApply (isim_mono with "H").
    iIntros (? ? ? ? ? ? ?) "[[D I] H]".
    iApply ("H" $! _ _ _ _ _ with "[D I]"). iFrame.
  Qed.

  Lemma wpsim_ret E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt r_src r_tgt
    :
    (FUpd (fairI (ident_tgt:=ident_tgt)) E ⊤ (Q r_src r_tgt))
      -∗
      (wpsim E r g Q ps pt (Ret r_src) (Ret r_tgt))
  .
  Proof.
    iIntros "> H".
    unfold wpsim. iIntros (? ? ? ? ?) "D".
    iApply isim_ret. iFrame.
  Qed.

  Lemma wpsim_tauL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q true pt itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt (Tau itr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauL. iFrame.
  Qed.

  Lemma wpsim_tauR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q ps true itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt itr_src (Tau itr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_tauR. iFrame.
  Qed.

  Lemma wpsim_chooseL E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    (∃ x, wpsim E r g Q true pt (ktr_src x) itr_tgt)
      -∗
      (wpsim E r g Q ps pt (trigger (Choose X) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "[% H]" (? ? ? ? ?) "D".
    iPoseProof ("H" $! _ _ _ _ _ with "D") as "H".
    iApply isim_chooseL. iExists _. iFrame.
  Qed.

  Lemma wpsim_chooseR E X r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    (∀ x, wpsim E r g Q ps true itr_src (ktr_tgt x))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Choose X) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_chooseR. iIntros (?).
    iPoseProof ("H" $! _ _ _ _ _ _ with "D") as "H". iFrame.
  Qed.

  Lemma wpsim_stateL E X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st_src
    :
    (St_src st_src)
    -∗ (St_src (fst (run st_src)) -∗ wpsim E r g Q true pt (ktr_src (snd (run st_src) : X)) itr_tgt)
    -∗ wpsim E r g Q ps pt (trigger (State run) >>= ktr_src) itr_tgt.
  Proof.
    unfold wpsim. iIntros "H0 H1" (? ? ? ? ?) "(D & C & E)". iApply isim_stateL.
    iAssert (⌜st_src0 = st_src⌝)%I as "%".
    { iApply (default_I_past_get_st_src with "D H0"); eauto. }
    subst.
    iPoseProof (default_I_past_update_st_src with "D H0") as "> [D H0]".
    iApply ("H1" with "D [H0 C E]"). iFrame.
  Qed.

  Lemma wpsim_lens_stateL E V (l : Lens.t _ V) X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st v
    :
    (Vw_src st l v)
    -∗ (Vw_src st l (fst (run v)) -∗ wpsim E r g Q true pt (ktr_src (snd (run v) : X)) itr_tgt)
    -∗ wpsim E r g Q ps pt (trigger (map_lens l (State run)) >>= ktr_src) itr_tgt.
  Proof.
    iIntros "S H". rewrite map_lens_State. iApply (wpsim_stateL with "S").
    iIntros "S". ss. unfold Vw_src.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply ("H" with "S").
  Qed.

  Lemma wpsim_stateR E X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
    -∗ (St_tgt (fst (run st_tgt)) -∗ wpsim E r g Q ps true itr_src (ktr_tgt (snd (run st_tgt) : X)))
    -∗ wpsim E r g Q ps pt itr_src (trigger (State run) >>= ktr_tgt).
  Proof.
    unfold wpsim. iIntros "H0 H1" (? ? ? ? ?) "(D & C & E)". iApply isim_stateR.
    iAssert (⌜st_tgt0 = st_tgt⌝)%I as "%".
    { iApply (default_I_past_get_st_tgt with "D H0"); eauto. }
    subst.
    iPoseProof (default_I_past_update_st_tgt with "D H0") as "> [D H0]".
    iApply ("H1" with "D [H0 C E]"). iFrame.
  Qed.

  Lemma wpsim_lens_stateR E V (l : Lens.t _ V) X run r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st v
    :
    (Vw_tgt st l v)
    -∗ (Vw_tgt st l (fst (run v)) -∗ wpsim E r g Q ps true itr_src (ktr_tgt (snd (run v) : X)))
    -∗ wpsim E r g Q ps pt itr_src (trigger (map_lens l (State run)) >>= ktr_tgt).
  Proof.
    iIntros "S H". rewrite map_lens_State. iApply (wpsim_stateR with "S").
    iIntros "S". ss. unfold Vw_tgt.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply ("H" with "S").
  Qed.

  Lemma wpsim_lens_getL V (l : Lens.t _ V) X (p : V -> X) E st v r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ((Vw_src st l v) ∧
       (wpsim E r g Q true pt (ktr_src (p v)) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (map_lens l (Get p)) >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "[D C]".
    rewrite map_lens_Get. rewrite Get_State. iApply isim_stateL. ss.
    iAssert (⌜Lens.view l st_src = v⌝)%I as "%".
    { iDestruct "H" as "[H1 _]". subst.
      iPoseProof (default_I_past_get_st_src with "D H1") as "%H". subst.
      rewrite Lens.view_set. auto.
    }
    rewrite H. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma wpsim_getL X (p : state_src -> X) E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ((St_src st) ∧
       (wpsim E r g Q true pt (ktr_src (p st)) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Get p) >>= ktr_src) itr_tgt)
  .
  Proof.
    iIntros "H". replace (Get p) with (map_lens Lens.id (Get p)) by ss.
    iApply wpsim_lens_getL. iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]". ss.
    Unshelve. all: eauto.
  Qed.

  Lemma wpsim_lens_getR V (l : Lens.t _ V) X (p : V -> X) E st v r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    ((Vw_tgt st l v) ∧
       (wpsim E r g Q ps true itr_src (ktr_tgt (p v))))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (map_lens l (Get p)) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "[D C]".
    rewrite map_lens_Get. rewrite Get_State. iApply isim_stateR. ss.
    iAssert (⌜Lens.view l st_tgt = v⌝)%I as "%".
    { iDestruct "H" as "[H1 _]". subst.
      iPoseProof (default_I_past_get_st_tgt with "D H1") as "%H". subst.
      rewrite Lens.view_set. auto.
    }
    rewrite H. iDestruct "H" as "[_ H]". iApply ("H" with "[D C]"). iFrame.
  Qed.

  Lemma wpsim_getR X (p : state_tgt -> X) E st r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    ((St_tgt st) ∧
       (wpsim E r g Q ps true itr_src (ktr_tgt (p st))))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Get p) >>= ktr_tgt))
  .
  Proof.
    iIntros "H". replace (Get p) with (map_lens Lens.id (Get p)) by ss.
    iApply wpsim_lens_getR. iSplit.
    - iDestruct "H" as "[H _]". iApply "H".
    - iDestruct "H" as "[_ H]". ss.
    Unshelve. all: eauto.
  Qed.

  Lemma wpsim_modifyL E f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st_src
    :
    (St_src st_src)
    -∗ (St_src (f st_src) -∗ wpsim E r g Q true pt (ktr_src tt) itr_tgt)
    -∗ wpsim E r g Q ps pt (trigger (Modify f) >>= ktr_src) itr_tgt.
  Proof.
    rewrite Modify_State. iIntros "H1 H2". iApply (wpsim_stateL with "H1"). ss.
  Qed.

  Lemma wpsim_lens_modifyL E V (l : Lens.t _ V) f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt ktr_src itr_tgt st v
    :
    (Vw_src st l v)
    -∗ (Vw_src st l (f v) -∗ wpsim E r g Q true pt (ktr_src tt) itr_tgt)
    -∗ wpsim E r g Q ps pt (trigger (map_lens l (Modify f)) >>= ktr_src) itr_tgt.
  Proof.
    rewrite map_lens_Modify.
    iIntros "H1 H2". iApply (wpsim_modifyL with "H1").
    iIntros "H". iApply "H2".
    unfold Lens.modify.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply "H".
  Qed.

  Lemma wpsim_modifyR E f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st_tgt
    :
    (St_tgt st_tgt)
    -∗ (St_tgt (f st_tgt) -∗ wpsim E r g Q ps true itr_src (ktr_tgt tt))
    -∗ wpsim E r g Q ps pt itr_src (trigger (Modify f) >>= ktr_tgt).
  Proof.
    rewrite Modify_State. iIntros "H1 H2". iApply (wpsim_stateR with "H1"). ss.
  Qed.

  Lemma wpsim_lens_modifyR E V (l : Lens.t _ V) f r g R_src R_tgt
    (Q : R_src -> R_tgt -> iProp)
    ps pt itr_src ktr_tgt st v
    :
    (Vw_tgt st l v)
    -∗ (Vw_tgt st l (f v) -∗ wpsim E r g Q ps true itr_src (ktr_tgt tt))
    -∗ wpsim E r g Q ps pt itr_src (trigger (map_lens l (Modify f)) >>= ktr_tgt).
  Proof.
    rewrite map_lens_Modify.
    iIntros "H1 H2". iApply (wpsim_modifyR with "H1").
    iIntros "H". iApply "H2".
    unfold Lens.modify.
    rewrite Lens.view_set. rewrite Lens.set_set.
    iApply "H".
  Qed.

  Lemma wpsim_tidL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    (wpsim E r g Q true pt (ktr_src tid) itr_tgt)
      -∗
      (wpsim E r g Q ps pt (trigger GetTid >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidL. iApply ("H" with "D").
  Qed.

  Lemma wpsim_tidR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
    :
    (wpsim E r g Q ps true itr_src (ktr_tgt tid))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger GetTid >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_tidR. iApply ("H" with "D").
  Qed.

  Lemma wpsim_fairL_prism o
        A lf ls
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white p i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white p i o) ls) -∗ (wpsim E r g Q true pt (ktr_src tt) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Fair (prism_fmap p fm)) >>= ktr_src) itr_tgt).
  Proof.
    unfold wpsim. iIntros "OWN H" (? ? ? ? ?) "(D & C & E)".
    iPoseProof (default_I_past_update_ident_source_prism with "D OWN") as "> [% [[% WHITES] D]]".
    { eauto. }
    { eauto. }
    iPoseProof ("H" with "WHITES [D C E]") as "H".
    { iFrame. }
    iApply isim_fairL. iExists _. iSplit; eauto.
  Qed.

  Lemma wpsim_fairL o lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      ((list_prop_sum (fun i => FairRA.white Prism.id i o) ls) -∗ (wpsim E r g Q true pt (ktr_src tt) itr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Fair fm) >>= ktr_src) itr_tgt).
  Proof.
    iIntros "WHITES K".
    rewrite <- (prism_fmap_id fm).
    iApply (wpsim_fairL_prism with "[WHITES] [K]"); eauto.
  Qed.

  Lemma wpsim_fairR_prism A lf ls
        (p : Prism.t _ A)
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => ObligationRA.duty (Prism.compose inrp p) i l ** ObligationRA.tax l) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty (Prism.compose inrp p) i l) ls)
         -*
         (list_prop_sum (fun i => FairRA.white (Prism.compose inrp p) i 1) lf)
         -*
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair (prism_fmap p fm)) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "OWN H"  (? ? ? ? ?) "(D & C & E)".
    iApply isim_fairR. iIntros (?) "%".
    iPoseProof (default_I_past_update_ident_target with "D OWN") as "> [[DUTY WHITE] D]".
    { rewrite prism_fmap_compose. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    iApply ("H" with "DUTY WHITE"). iFrame.
  Qed.

  Lemma wpsim_fairR lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun '(i, l) => ObligationRA.duty inrp i l ** ObligationRA.tax l) ls)
      -∗
      ((list_prop_sum (fun '(i, l) => ObligationRA.duty inrp i l) ls)
         -*
         (list_prop_sum (fun i => FairRA.white inrp i 1) lf)
         -*
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "DUTY K".
    rewrite <- (prism_fmap_id fm).
    iApply (wpsim_fairR_prism with "[DUTY] [K]"); eauto.
  Qed.

  Lemma wpsim_fairR_simple lf ls
        E fm r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src ktr_tgt
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i ls)
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (list_prop_sum (fun i => FairRA.black_ex inrp i 1) ls)
      -∗
      ((list_prop_sum (fun i => FairRA.black_ex inrp i 1) ls)
         -*
         (list_prop_sum (fun i => FairRA.white inrp i 1) lf)
         -*
         wpsim E r g Q ps true itr_src (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt itr_src (trigger (Fair fm) >>= ktr_tgt))
  .
  Proof.
    iIntros "A B". iApply (wpsim_fairR with "[A]"); eauto.
    { instantiate (1:= List.map (fun i => (i, [])) ls). i. specialize (SUCCESS _ IN). rewrite List.map_map. ss.
      replace (List.map (λ x : ident_tgt, x) ls) with ls; auto. clear. induction ls; ss; eauto. f_equal. auto.
    }
    { iApply list_prop_sum_map. 2: iFrame. i. ss. iIntros "BLK". iSplitL; auto. iApply ObligationRA.black_to_duty. auto. }
    { iIntros "S F". iApply ("B" with "[S]"). 2: iFrame. iApply list_prop_sum_map_inv. 2: iFrame.
      i; ss. iIntros "D". iApply ObligationRA.duty_to_black. iFrame.
    }
  Qed.

  Lemma wpsim_UB E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src itr_tgt
    :
    ⊢ (wpsim E r g Q ps pt (trigger Undefined >>= ktr_src) itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros (? ? ? ? ?) "D".
    iApply isim_UB. auto.
  Qed.

  Lemma wpsim_observe E fn args r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    (∀ ret, wpsim E g g Q true true (ktr_src ret) (ktr_tgt ret))
      -∗
      (wpsim E r g Q ps pt (trigger (Observe fn args) >>= ktr_src) (trigger (Observe fn args) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_observe. iIntros (?). iApply ("H" with "D").
  Qed.

  Lemma wpsim_yieldL E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    (wpsim E r g Q true pt (ktr_src tt) (trigger (Yield) >>= ktr_tgt))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_yieldL. iApply ("H" with "D").
  Qed.

  Lemma wpsim_yieldR_strong E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         (FUpd (fairI (ident_tgt:=ident_tgt)) E ⊤
               (wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K".
    unfold wpsim. iIntros (? ? ? ? ?) "(D & C & E)".
    iPoseProof (default_I_past_update_ident_thread with "D H") as "> [[B W] [[[[[[D0 D1] D2] D3] D4] D5] D6]]".
    iAssert ((fairI (ident_tgt:=ident_tgt)) ** (wsat ** OwnE E)) with "[C D5 D6 E]" as "C".
    { iFrame. }
    iPoseProof ("K" with "B W C") as "> [D5 [D6 [E K]]]".
    iApply isim_yieldR. unfold I, fairI. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & C & E) %".
    iApply ("K" with "[D C E]"). iFrame. iExists _. eauto.
  Qed.

  Lemma wpsim_sync_strong E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         (FUpd (fairI (ident_tgt:=ident_tgt)) E ⊤
               (wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K".
    unfold wpsim. iIntros (? ? ? ? ?) "(D & C & E)".
    iPoseProof (default_I_past_update_ident_thread with "D H") as "> [[B W] [[[[[[D0 D1] D2] D3] D4] D5] D6]]".
    iAssert ((fairI (ident_tgt:=ident_tgt)) ** (wsat ** OwnE E)) with "[C D5 D6 E]" as "C".
    { iFrame. }
    iPoseProof ("K" with "B W C") as "> (D5 & C & E & K)".
    iApply isim_sync. unfold I. iFrame. iFrame.
    iIntros (? ? ? ? ? ?) "(D & C & E) %".
    iApply ("K" with "[D C E]"). iFrame. iExists _. eauto.
  Qed.

  Lemma wpsim_yieldR E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        (TOP: ⊤ ⊆ E)
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "H K". iApply wpsim_discard; [eassumption|].
    iApply (wpsim_yieldR_strong with "H"). iIntros "DUTY WHITE".
    iModIntro. iApply ("K" with "DUTY WHITE").
  Qed.

  Lemma wpsim_sync E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt l
        (TOP: ⊤ ⊆ E)
    :
    (ObligationRA.duty inlp tid l ** ObligationRA.tax l)
      -∗
      ((ObligationRA.duty inlp tid l)
         -*
         (FairRA.white_thread (S:=_))
         -*
         wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt))
      -∗
      (wpsim E r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "H K". iApply wpsim_discard; [eassumption|].
    iApply (wpsim_sync_strong with "H"). iIntros "DUTY WHITE".
    iModIntro. iApply ("K" with "DUTY WHITE").
  Qed.

  (* Note:  *)
  (*   MUpd _ fairI topset topset P *)
  (*        is a generalized version of I * (I -* P) *)
  Lemma wpsim_yieldR_simple r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    FUpd (fairI (ident_tgt:=ident_tgt)) ⊤ ⊤
         ((FairRA.black_ex inlp tid 1)
            **
            ((FairRA.black_ex inlp tid 1)
               -*
               (FairRA.white_thread (S:=_))
               -*
               wpsim ⊤ r g Q ps true (trigger (Yield) >>= ktr_src) (ktr_tgt tt)))
         -∗
         (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt))
  .
  Proof.
    iIntros "> [H K]". iApply (wpsim_yieldR with "[H]").
    { auto. }
    { iPoseProof (ObligationRA.black_to_duty with "H") as "H". iFrame. }
    iIntros "B W". iApply ("K" with "[B] [W]"); ss.
    { iApply ObligationRA.duty_to_black. auto. }
  Qed.

  Lemma wpsim_sync_simple r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt ktr_src ktr_tgt
    :
    FUpd (fairI (ident_tgt:=ident_tgt)) ⊤ ⊤
         ((FairRA.black_ex inlp tid 1)
            **
            ((FairRA.black_ex inlp tid 1)
               -*
               (FairRA.white_thread (S:=_))
               -*
               wpsim ⊤ g g Q true true (ktr_src tt) (ktr_tgt tt)))
      -∗
      (wpsim ⊤ r g Q ps pt (trigger (Yield) >>= ktr_src) (trigger (Yield) >>= ktr_tgt)).
  Proof.
    iIntros "> [H K]". iApply (wpsim_sync with "[H]").
    { auto. }
    { iPoseProof (ObligationRA.black_to_duty with "H") as "H". iFrame. }
    iIntros "B W". iApply ("K" with "[B] [W]"); ss.
    { iApply ObligationRA.duty_to_black. auto. }
  Qed.

  Lemma wpsim_reset E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        ps pt itr_src itr_tgt
    :
    (wpsim E r g Q false false itr_src itr_tgt)
      -∗
      (wpsim E r g Q ps pt itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_reset. iApply ("H" with "D").
  Qed.

  Lemma wpsim_progress E r g R_src R_tgt
        (Q: R_src -> R_tgt -> iProp)
        itr_src itr_tgt
    :
    (wpsim E g g Q false false itr_src itr_tgt)
      -∗
      (wpsim E r g Q true true itr_src itr_tgt)
  .
  Proof.
    unfold wpsim. iIntros "H" (? ? ? ? ?) "D".
    iApply isim_progress. iApply ("H" with "D").
  Qed.

  Definition ibot5 { T0 T1 T2 T3 T4} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3): iProp := False.
  Definition ibot7 { T0 T1 T2 T3 T4 T5 T6} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5): iProp := False.

End STATE.

From Fairness Require Export Red IRed.

Ltac lred := repeat (prw _red_gen 1 2 0).
Ltac rred := repeat (prw _red_gen 1 1 0).

From Fairness Require Export LinkingRed.

Ltac lred2 := (prw ltac:(red_tac itree_class) 1 2 0).
Ltac rred2 := (prw ltac:(red_tac itree_class) 1 1 0).
