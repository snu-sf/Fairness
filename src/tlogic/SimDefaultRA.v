From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import ITreeLib pind.
Require Import Program.
From Fairness Require Import PCM IProp IPM IPropAux.
From Fairness Require Import Mod FairBeh.
From Fairness Require Import Axioms.
From Fairness Require Import NatMapRALarge MonotoneRA RegionRA FairnessRA IndexedInvariants ObligationRA OpticsInterp.

Set Implicit Arguments.

Section PAIR.
  Variable A: Type.
  Variable B: Type.

  Context `{IN: @GRA.inG (Auth.t (Excl.t (A * B))) Σ}.
  Context `{INA: @GRA.inG (Auth.t (Excl.t A)) Σ}.
  Context `{INB: @GRA.inG (Auth.t (Excl.t B)) Σ}.

  Definition pair_sat: iProp :=
    ∃ a b,
      (OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
        **
        (OwnM (Auth.black (Excl.just a: @Excl.t A)))
        **
        (OwnM (Auth.black (Excl.just b: @Excl.t B)))
  .

  Lemma pair_access_fst a
    :
    (OwnM (Auth.white (Excl.just a: @Excl.t A)))
      -∗
      (pair_sat)
      -∗
      (∃ b, (OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
              **
              (∀ a,
                  ((OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
                     -*
                     #=> ((OwnM (Auth.white (Excl.just a: @Excl.t A))) ** (pair_sat))))).
  Proof.
    iIntros "H [% [% [[H0 H1] H2]]]".
    iPoseProof (black_white_equal with "H1 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H1 H") as "> [H1 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.

  Lemma pair_access_snd b
    :
    (OwnM (Auth.white (Excl.just b: @Excl.t B)))
      -∗
      (pair_sat)
      -∗
      (∃ a, (OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
              **
              (∀ b,
                  ((OwnM (Auth.white (Excl.just (a, b): @Excl.t (A * B))))
                     -*
                     #=> ((OwnM (Auth.white (Excl.just b: @Excl.t B))) ** (pair_sat))))).
  Proof.
    iIntros "H [% [% [[H0 H1] H2]]]".
    iPoseProof (black_white_equal with "H2 H") as "%". subst.
    iExists _. iFrame. iIntros (?) "H0".
    iPoseProof (black_white_update with "H2 H") as "> [H2 H]".
    iModIntro. iFrame. iExists _, _. iFrame.
  Qed.
End PAIR.



Section INVARIANT.
  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Definition stateSrcRA: URA.t := Auth.t (Excl.t (option state_src)).
  Definition stateTgtRA: URA.t := Auth.t (Excl.t (option state_tgt)).
  Definition identSrcRA: URA.t := FairRA.srct ident_src.
  Definition identTgtRA: URA.t := FairRA.tgtt ident_tgt.
  Definition ThreadRA: URA.t := Auth.t (NatMapRALarge.t unit).
  Definition EdgeRA: URA.t := Region.t (nat * nat * Ord.t).
  Definition ArrowShotRA: URA.t := @FiniteMap.t (OneShot.t unit).

  Local Notation index := nat.
  Context `{Vars : index -> Type}.

  Definition ArrowRA: URA.t :=
    Regions.t (fun x => ((sum_tid ident_tgt) * nat * Ord.t * Qp * nat * (Vars x))%type).

  Context `{Σ : GRA.t}.
  Context `{Invs : @IInvSet Σ Vars}.

  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG stateSrcRA Σ}.
  Context `{STATETGT: @GRA.inG stateTgtRA Σ}.
  Context `{IDENTSRC: @GRA.inG identSrcRA Σ}.
  Context `{IDENTTGT: @GRA.inG identTgtRA Σ}.
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ONESHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG ArrowRA Σ}.

  (* Works for formulas with index < x. *)
  Definition fairI x : iProp :=
    (ObligationRA.edges_sat)
      ∗
      (ObligationRA.arrows_sats (S := sum_tid ident_tgt) x).

  Definition default_I x :
    TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      ((OwnM (Auth.black (Some ths: (NatMapRALarge.t unit)): ThreadRA))
         ∗
         (OwnM (Auth.black (Excl.just (Some st_src): @Excl.t (option state_src)): stateSrcRA))
         ∗
         (OwnM (Auth.black (Excl.just (Some st_tgt): @Excl.t (option state_tgt)): stateTgtRA))
         ∗
         (FairRA.sat_source im_src)
         ∗
         (FairRA.sat_target im_tgt ths)
         ∗
         (ObligationRA.edges_sat)
         ∗
         (ObligationRA.arrows_sats (S := sum_tid ident_tgt) x)
         ∗
         (ObligationRA.arrows_auth (S := sum_tid ident_tgt) x)
      )%I
  .

  Definition default_I_past (tid: thread_id) x
    : TIdSet.t -> (@imap ident_src owf) -> (@imap (sum_tid ident_tgt) nat_wf) -> state_src -> state_tgt -> iProp :=
    fun ths im_src im_tgt st_src st_tgt =>
      (∃ im_tgt0,
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ∗ (default_I x ths im_src im_tgt0 st_src st_tgt))%I.

  Definition own_thread (tid: thread_id): iProp :=
    (OwnM (Auth.white (NatMapRALarge.singleton tid tt: NatMapRALarge.t unit): ThreadRA)).

  Lemma own_thread_unique tid0 tid1
    :
    ⊢ (own_thread tid0)
      -∗
      (own_thread tid1)
      -∗
      ⌜tid0 <> tid1⌝.
  Proof.
    iIntros "OWN0 OWN1". iCombine "OWN0 OWN1" as "OWN".
    iOwnWf "OWN". ur in H. apply NatMapRALarge.singleton_unique in H.
    iPureIntro. auto.
  Qed.

  Lemma default_I_update_st_src x ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    ⊢ (default_I x ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_src'): @Excl.t (option state_src)): stateSrcRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_src1): @Excl.t (option state_src)))
                ∗ default_I x ths im_src im_tgt st_src1 st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_update with "B OWN") as "> [B OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_update_st_tgt x ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_tgt'): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_tgt1): @Excl.t (option state_tgt)))
                ∗ default_I x ths im_src im_tgt st_src st_tgt1).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_update with "C OWN") as "> [C OWN]".
    iModIntro. iFrame.
  Qed.

  Lemma default_I_get_st_src x ths im_src im_tgt st_src st_tgt st
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_src)): stateSrcRA))
      -∗
      ⌜st_src = st⌝.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_equal with "B OWN") as "%". clarify.
  Qed.

  Lemma default_I_get_st_tgt x ths im_src im_tgt st_src st_tgt st
    :
    ⊢ (default_I x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] OWN".
    iPoseProof (black_white_equal with "C OWN") as "%". clarify.
  Qed.

  Lemma default_I_thread_alloc x n ths0 im_src im_tgt0 st_src st_tgt
        tid ths1 im_tgt1
        (THS: TIdSet.add_new tid ths0 ths1)
        (TID_TGT : fair_update im_tgt0 im_tgt1 (prism_fmap inlp (fun i => if tid_dec i tid then Flag.success else Flag.emp)))
    :
    ⊢
      (default_I x ths0 im_src im_tgt0 st_src st_tgt)
      -∗
      #=> (own_thread tid ∗ ObligationRA.duty n inlp tid [] ∗ default_I x ths1 im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]]".
    iPoseProof (OwnM_Upd with "A") as "> [A TH]".
    { apply Auth.auth_alloc.
      eapply (@NatMapRALarge.add_local_update unit ths0 tid tt). inv THS. auto.
    }
    iPoseProof (FairRA.target_add_thread with "E") as "> [E BLACK]"; [eauto|eauto|].
    iModIntro. inv THS. iFrame.
    iApply ObligationRA.black_to_duty. iFrame.
  Qed.

  Lemma default_I_update_ident_thread x n ths im_src im_tgt0 st_src st_tgt
        tid im_tgt1 l
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap inlp (tids_fmap tid ths)))
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp tid l ∗ ObligationRA.tax (List.map fst l))
      -∗
      #=> (ObligationRA.duty n inlp tid l ∗ FairRA.white_thread (S:=_) ∗ default_I x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]] DUTY".
    iPoseProof (ObligationRA.target_update_thread with "E DUTY") as "RES". eauto.
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iMod ("RES" with "ARROW") as "[ARROW [E [DUTY WHITE]]]". iFrame.
    iApply "K". iFrame.
  Qed.

  Lemma default_I_update_ident_target x n A lf ls
        (p: Prism.t ident_tgt A)
        ths im_src im_tgt0 st_src st_tgt
        fm im_tgt1
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap (inrp ⋅ p)%prism fm))
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (n < x) ->
    ⊢
      (default_I x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l ∗ ObligationRA.tax (List.map fst l)) ls)
      -∗
      #=> ((list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l) ls)
             ∗
             (list_prop_sum (fun i => FairRA.white (Id:=_) (inrp ⋅ p)%prism i 1) lf)
             ∗
             default_I x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    unfold default_I. iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]] DUTY".
    iPoseProof (ObligationRA.target_update with "E DUTY") as "RES". 1,2,3,4: eauto.
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iMod ("RES" with "ARROW") as "[ARROW [E [DUTY WHITE]]]". iFrame.
    iApply "K". iFrame.
  Qed.

  Lemma default_I_update_ident_source x lf ls o
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    ⊢
      (default_I x ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                ∗
                (list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
                ∗
                default_I x ths im_src1 im_tgt st_src st_tgt).
  Proof.
    unfold default_I. iIntros "[A [B [C [D [E [F G]]]]]] WHITES".
    iPoseProof (FairRA.source_update with "D WHITES") as "> [% [[% D] WHITE]]".
    { eauto. }
    { eauto. }
    iModIntro. iExists _. iFrame. auto.
  Qed.

  Lemma arrows_sat_sub x n ths im_src im_tgt st_src st_tgt
    :
    (n < x) ->
    ⊢ SubIProp (ObligationRA.arrows_sat n (S := sum_tid ident_tgt)) (default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros (LT) "[A [B [C [D [E [F [G H]]]]]]]".
    iMod (Regions.nsats_sat_sub with "G") as "[ARROW K]". apply LT.
    iFrame. iModIntro. iFrame.
  Qed.

  Lemma edges_sat_sub x ths im_src im_tgt st_src st_tgt
    :
    ⊢ SubIProp (ObligationRA.edges_sat) (default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros "[A [B [C [D [E [F G]]]]]]". iModIntro. iFrame. auto.
  Qed.

  Lemma default_I_past_update_st_src tid x ths im_src im_tgt st_src0 st_tgt st_src' st_src1
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src0 st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_src'): @Excl.t (option state_src)): stateSrcRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_src1): @Excl.t (option state_src)))
                ∗ default_I_past tid x ths im_src im_tgt st_src1 st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_st_src with "D H") as "> [H D]".
    iModIntro. iSplitL "H"; auto. unfold default_I_past. eauto.
  Qed.

  Lemma default_I_past_update_st_tgt x tid ths im_src im_tgt st_src st_tgt0 st_tgt' st_tgt1
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt0)
      -∗
      (OwnM (Auth.white (Excl.just (Some st_tgt'): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      #=> (OwnM (Auth.white (Excl.just (Some st_tgt1): @Excl.t (option state_tgt)))
                ∗ default_I_past tid x ths im_src im_tgt st_src st_tgt1).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_st_tgt with "D H") as "> [H D]".
    iModIntro. iSplitL "H"; auto. unfold default_I_past. eauto.
  Qed.

  Lemma default_I_past_get_st_src x tid ths im_src im_tgt st_src st_tgt st
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_src)): stateSrcRA))
      -∗
      ⌜st_src = st⌝.
  Proof.
    iIntros "[% [% D]] H". iApply (default_I_get_st_src with "D H").
  Qed.

  Lemma default_I_past_get_st_tgt x tid ths im_src im_tgt st_src st_tgt st
    :
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (OwnM (Auth.white (Excl.just (Some st): @Excl.t (option state_tgt)): stateTgtRA))
      -∗
      ⌜st_tgt = st⌝.
  Proof.
    iIntros "[% [% D]] H". iApply (default_I_get_st_tgt with "D H").
  Qed.

  Lemma default_I_past_update_ident_thread x n ths im_src im_tgt st_src st_tgt
        tid l
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths im_src im_tgt st_src st_tgt)
      -∗
      (ObligationRA.duty n inlp tid l ∗ ObligationRA.tax (List.map fst l))
      -∗
      #=> (ObligationRA.duty n inlp tid l ∗ FairRA.white_thread (S:=_) ∗ default_I x ths im_src im_tgt st_src st_tgt).
  Proof.
    iIntros (LT) "[% [% D]] H". iApply (default_I_update_ident_thread with "D H"). all: eauto.
  Qed.

  Lemma default_I_past_update_ident_target A tid x n lf ls
        (p: Prism.t ident_tgt A)
        ths im_src im_tgt0 st_src st_tgt
        fm im_tgt1
        (UPD: fair_update im_tgt0 im_tgt1 (prism_fmap (inrp ⋅ p)%prism fm))
        (SUCCESS: forall i (IN: fm i = Flag.success), List.In i (List.map fst ls))
        (FAIL: forall i (IN: List.In i lf), fm i = Flag.fail)
        (NODUP: List.NoDup lf)
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths im_src im_tgt0 st_src st_tgt)
      -∗
      (list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l ∗ ObligationRA.tax (List.map fst l)) ls)
      -∗
      #=> ((list_prop_sum (fun '(i, l) => ObligationRA.duty n (inrp ⋅ p)%prism i l) ls)
             ∗
             (list_prop_sum (fun i => FairRA.white (Id:=_) (inrp ⋅ p)%prism i 1) lf)
             ∗
             default_I_past tid x ths im_src im_tgt1 st_src st_tgt).
  Proof.
    iIntros (LT) "[% [% D]] H".
    iPoseProof (default_I_update_ident_target with "D H") as "> [H0 [H1 D]]". 1,2,3,4,5: eauto.
    { instantiate (1:=(fun i =>
                         match i with
                         | inl i => im_tgt2 (inl i)
                         | inr i => im_tgt1 (inr i)
                         end)).
      ii. specialize (UPD i). specialize (H i).
      unfold prism_fmap, tids_fmap in *; ss. unfold is_inl, is_inr in *; ss. des_ifs.
      { rewrite <- H. auto. }
      { rewrite UPD. auto. }
      { etrans; eauto. }
    }
    iModIntro. iFrame.
    unfold default_I_past. iExists _. iSplit; eauto. iPureIntro.
    ii. specialize (UPD i). specialize (H i).
    unfold prism_fmap, tids_fmap in *; ss. unfold is_inl in *; ss. des_ifs.
    { rewrite UPD. auto. }
    { rewrite <- H. auto. }
  Qed.

  Lemma default_I_past_update_ident_source tid x lf ls o
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    ⊢
      (default_I_past tid x ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white Prism.id i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 fm⌝)
                ∗
                (list_prop_sum (fun i => FairRA.white Prism.id i o) ls)
                ∗
                default_I_past tid x ths im_src1 im_tgt st_src st_tgt).
  Proof.
    iIntros "[% [% D]] H".
    iPoseProof (default_I_update_ident_source with "D H") as "> [% [% [H D]]]"; [eauto|eauto|..].
    iModIntro. unfold default_I_past. iExists _. iSplitR. eauto. iFrame. iExists _. iFrame. auto.
  Qed.

  Lemma default_I_past_update_ident_source_prism A tid x lf ls o
        (p: Prism.t ident_src A)
        ths im_src0 im_tgt st_src st_tgt
        fm
        (FAIL: forall i (IN: fm i = Flag.fail), List.In i lf)
        (SUCCESS: forall i (IN: List.In i ls), fm i = Flag.success)
    :
    ⊢
      (default_I_past tid x ths im_src0 im_tgt st_src st_tgt)
      -∗
      (list_prop_sum (fun i => FairRA.white p i Ord.one) lf)
      -∗
      #=> (∃ im_src1,
              (⌜fair_update im_src0 im_src1 (prism_fmap p fm)⌝)
                ∗
                (list_prop_sum (fun i => FairRA.white p i o) ls)
                ∗
                default_I_past tid x ths im_src1 im_tgt st_src st_tgt).
  Proof.
    iIntros "D H".
    iPoseProof (default_I_past_update_ident_source with "D [H]") as "> [% [% [H D]]]".
    { instantiate (1:=List.map (Prism.review p) lf). instantiate (1:=prism_fmap p fm).
      i. unfold prism_fmap in IN. des_ifs.
      eapply Prism.review_preview in Heq. subst.
      eapply in_map. auto.
    }
    { instantiate (1:=List.map (Prism.review p) ls).
      i. eapply in_map_iff in IN. des. subst.
      unfold prism_fmap. rewrite Prism.preview_review. auto.
    }
    { iApply (list_prop_sum_map with "H"). i.
      iIntros "H". iApply (FairRA.white_prism_id with "H").
    }
    iModIntro. iExists _. iFrame. iSplit; auto.
    iApply (list_prop_sum_map_inv with "H"). i.
    iIntros "H". iApply (FairRA.white_prism_id_rev with "H").
  Qed.

  Lemma default_I_past_final ths0 im_src im_tgt st_src st_tgt
        tid x n
    :
    (n < x) ->
    ⊢
      (default_I_past tid x ths0 im_src im_tgt st_src st_tgt)
      -∗
      (own_thread tid ∗ ObligationRA.duty n inlp tid [])
      -∗
      #=> (∃ ths1,
              (⌜NatMap.remove tid ths0 = ths1⌝)
                ∗
                (default_I x ths1 im_src im_tgt st_src st_tgt)).
  Proof.
    iIntros (LT) "[% [% D]] [OWN DUTY]".
    iPoseProof (default_I_update_ident_thread with "D [DUTY]") as "> [DUTY [_ D]]".
    { eauto. }
    { eauto. }
    { iSplitL; eauto. }
    unfold default_I. iPoseProof "D" as "[A [B [C [D [E [F G]]]]]]".
    iCombine "A OWN" as "A".
    iPoseProof (OwnM_Upd with "A") as "> X".
    { apply Auth.auth_dealloc. eapply (@NatMapRALarge.remove_local_update unit ths0 _ _). }
    iPoseProof (FairRA.target_remove_thread with "E [DUTY]") as "> E".
    { iPoseProof "DUTY" as "[% [% [A [[B %] %]]]]". destruct rs; ss. subst. iFrame. }
    iModIntro. iExists _. iFrame. auto.
  Qed.

End INVARIANT.

Section INIT.

  Context `{Σ: GRA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable ident_src: ID.
  Variable ident_tgt: ID.

  Local Notation index := nat.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.

  (* Invariant related default RAs *)
  Context `{OWNESRA : @GRA.inG OwnEsRA Σ}.
  Context `{OWNDSRA : @GRA.inG OwnDsRA Σ}.
  Context `{IINVSETRA : @GRA.inG (IInvSetRA Vars) Σ}.

  (* State related default RAs *)
  Context `{THDRA: @GRA.inG ThreadRA Σ}.
  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{IDENTSRC: @GRA.inG (identSrcRA ident_src) Σ}.
  Context `{IDENTTGT: @GRA.inG (identTgtRA ident_tgt) Σ}.

  (* Liveness logic related default RAs *)
  Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
  Context `{EDGERA: @GRA.inG EdgeRA Σ}.
  Context `{ARROWSHOTRA: @GRA.inG ArrowShotRA Σ}.
  Context `{ARROWRA: @GRA.inG (@ArrowRA ident_tgt Vars) Σ}.


  Definition default_initial_res
    : Σ :=
    (@GRA.embed _ _ OWNESRA ((fun _ => Some ⊤) : OwnEsRA))
      ⋅
      (@GRA.embed _ _ IINVSETRA ((fun n => @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)) : IInvSetRA Vars))
      ⋅
      (@GRA.embed _ _ THDRA (Auth.black (Some (NatMap.empty unit): NatMapRALarge.t unit)))
      ⋅
      (@GRA.embed _ _ STATESRC (Auth.black (Excl.just None: @Excl.t (option state_src)) ⋅ (Auth.white (Excl.just None: @Excl.t (option state_src)): stateSrcRA state_src)))
      ⋅
      (@GRA.embed _ _ STATETGT (Auth.black (Excl.just None: @Excl.t (option state_tgt)) ⋅ (Auth.white (Excl.just None: @Excl.t (option state_tgt)): stateTgtRA state_tgt)))
      ⋅
      (@GRA.embed _ _ IDENTSRC (@FairRA.source_init_resource ident_src))
      ⋅
      (@GRA.embed _ _ IDENTTGT ((fun _ => Fuel.black 0 1%Qp): identTgtRA ident_tgt))
      ⋅
      (@GRA.embed _ _ EDGERA ((fun _ => OneShot.pending _ 1%Qp): EdgeRA))
      ⋅
      (@GRA.embed _ _ ARROWRA ((@Regions.nauth_ra _ 0): @ArrowRA ident_tgt Vars))
      (* (@GRA.embed _ _ ARROWRA ((fun _ => (fun _ => OneShot.pending _ 1%Qp)): @ArrowRA ident_tgt Vars)) *)
  .

  Lemma own_threads_init ths
    :
    (OwnM (Auth.black (Some (NatMap.empty unit): NatMapRALarge.t unit)))
      -∗
      (#=>
         ((OwnM (Auth.black (Some ths: NatMapRALarge.t unit)))
            ∗
            (natmap_prop_sum ths (fun tid _ => own_thread tid)))).
  Proof.
    pattern ths. revert ths. eapply nm_ind.
    { iIntros "OWN". iModIntro. iFrame. }
    i. iIntros "OWN".
    iPoseProof (IH with "OWN") as "> [OWN SUM]".
    iPoseProof (OwnM_Upd with "OWN") as "> [OWN0 OWN1]".
    { eapply Auth.auth_alloc. eapply (@NatMapRALarge.add_local_update unit m k v); eauto. }
    iModIntro. iFrame. destruct v. iApply (natmap_prop_sum_add with "SUM OWN1").
  Qed.

  Lemma default_initial_res_init x n (LT : n < x)
    :
    (Own (default_initial_res))
      ⊢
      (∀ ths (st_src : state_src) (st_tgt : state_tgt) im_tgt o,
          #=> (∃ im_src,
                  (default_I x ths im_src im_tgt st_src st_tgt)
                    ∗
                    (natmap_prop_sum ths (fun tid _ => ObligationRA.duty n inlp tid []))
                    ∗
                    (natmap_prop_sum ths (fun tid _ => own_thread tid))
                    ∗
                    (FairRA.whites Prism.id (fun _ => True: Prop) o)
                    ∗
                    (FairRA.blacks Prism.id (fun i => match i with | inr _ => True | _ => False end: Prop))
                    ∗
                    (St_src st_src)
                    ∗
                    (St_tgt st_tgt)
                    ∗
                    wsat_auth x
                    ∗
                    wsats x
                    ∗
                    OwnEs ∅
      )).
  Proof.
    iIntros "OWN" (? ? ? ? ?).
    iDestruct "OWN" as "[[[[[[[[ENS WSATS] OWN0] [OWN1 OWN2]] [OWN3 OWN4]] OWN5] OWN6] OWN7] OWN8]".
    iPoseProof (black_white_update with "OWN1 OWN2") as "> [OWN1 OWN2]".
    iPoseProof (black_white_update with "OWN3 OWN4") as "> [OWN3 OWN4]".
    iPoseProof (OwnM_Upd with "OWN6") as "> OWN6".
    { instantiate (1:=FairRA.target_init_resource im_tgt).
      unfold FairRA.target_init_resource.
      erewrite ! (@unfold_pointwise_add (id_sum nat ident_tgt) (Fuel.t nat)).
      apply pointwise_updatable. i.
      rewrite URA.add_comm. exact (@Fuel.success_update nat _ 0 (im_tgt a)).
    }
    iPoseProof (FairRA.target_init with "OWN6") as "[[H0 H1] H2]".
    iPoseProof (FairRA.source_init with "OWN5") as "> [% [H3 H4]]".
    iExists f. unfold default_I. iFrame.

    iPoseProof (wsats_init_zero with "WSATS") as "W".
    iPoseProof ((wsats_allocs _ x) with "W") as "[WA WS]". lia. iFrame.
    iPoseProof (own_threads_init with "OWN0") as "> [OWN0 H]". iFrame.

    iModIntro. iSplitL "OWN7 OWN8"; [iSplitL "OWN7"|].
    { iExists []. iSplitL; [|auto].
      iApply (OwnM_extends with "OWN7").
      apply pointwise_extends. i. destruct a; ss; reflexivity.
    }
    { iAssert (ObligationRA.arrows_sats 0)%I as "INIT".
      { unfold ObligationRA.arrows_sats, Regions.nsats. ss. }
      iPoseProof (Regions.nsats_allocs _ (x1:=0) (x2:=x) with "[OWN8]") as "[A S]". lia.
      { iFrame. eauto. }
      iFrame.
    }

    iSplitR "H2"; [|iSplitL "H2"].
    { iApply natmap_prop_sum_impl; [|eauto]. i. ss.
      iApply ObligationRA.black_to_duty.
    }
    { iPoseProof (FairRA.blacks_prism_id with "H2") as "H".
      iApply (FairRA.blacks_impl with "H").
      i. des_ifs. esplits; eauto.
    }
    { unfold OwnE_satall. ss. }
  Qed.

End INIT.
