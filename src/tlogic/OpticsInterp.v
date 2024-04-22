From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Import Optics IProp IPM PCM.

Set Implicit Arguments.

From stdpp Require Import coPset gmap namespaces.
From Fairness Require Export SimDefaultRA FancyUpdate.

Require Import Program.

Section STATE.

  Context `{Σ: GRA.t}.

  Class ViewInterp {S V} (l : Lens.t S V) (SI : S -> iProp) (VI : V -> iProp) := {
      view_interp : forall s, (SI s) ⊢ (VI (Lens.view l s) ∗ ∀ x, VI x -∗ SI (Lens.set l x s))
    }.

  Definition interp_prod {A B} (SA: A -> iProp) (SB: B -> iProp):
    (A * B -> iProp) :=
    fun '(sa, sb) => SA sa ** SB sb.

  Global Program Instance ViewInterp_fstl {A B}
         (SA: A -> iProp) (SB: B -> iProp)
    : ViewInterp fstl (interp_prod SA SB) SA.
  Next Obligation.
  Proof.
    iIntros "[H0 H1]". iSplitL "H0".
    { iExact "H0". }
    { iIntros (?) "H0". iFrame. }
  Qed.

  Global Program Instance ViewInterp_sndl {A B}
         (SA: A -> iProp) (SB: B -> iProp)
    : ViewInterp sndl (interp_prod SA SB) SB.
  Next Obligation.
  Proof.
    iIntros "[H0 H1]". iSplitL "H1".
    { iExact "H1". }
    { iIntros (?) "H1". iFrame. }
  Qed.

  Global Program Instance ViewInterp_id {S} (SI: S -> iProp): ViewInterp Lens.id SI SI.
  Next Obligation.
  Proof.
    iIntros "H". iSplitL "H".
    { iExact "H". }
    { iIntros (?) "H". iExact "H". }
  Qed.

  Global Program Instance ViewInterp_compose {A B C}
         {lab: Lens.t A B}
         {lbc: Lens.t B C}
         (SA: A -> iProp) (SB: B -> iProp) (SC: C -> iProp)
         `{VAB: ViewInterp _ _ lab SA SB}
         `{VBC: ViewInterp _ _ lbc SB SC}
    :
    ViewInterp (Lens.compose lab lbc) SA SC.
  Next Obligation.
  Proof.
    iIntros "H".
    iPoseProof (view_interp with "H") as "[H K0]".
    iPoseProof (view_interp with "H") as "[H K1]".
    iSplitL "H"; [auto|]. iIntros (?) "H".
    iApply "K0". iApply "K1". iApply "H".
  Qed.

  Definition N_state_src := (nroot .@ "_state_src").
  Definition E_state_src: coPset := ↑ N_state_src.
  Definition N_state_tgt := (nroot .@ "_state_tgt").
  Definition E_state_tgt: coPset := ↑ N_state_tgt.

  Variable state_src: Type.
  Variable state_tgt: Type.

  (* Variable ident_src: ID. *)
  (* Variable ident_tgt: ID. *)

  Context `{Invs : @InvSet Σ}.

  Context `{STATESRC: @GRA.inG (stateSrcRA state_src) Σ}.
  Context `{STATETGT: @GRA.inG (stateTgtRA state_tgt) Σ}.
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

  Definition St_src (st_src: state_src): iProp :=
    OwnM (Auth.white (Excl.just (Some st_src): @Excl.t (option state_src)): stateSrcRA state_src).

  Definition Vw_src (st: state_src) {V} (l : Lens.t state_src V) (v : V) : iProp :=
    St_src (Lens.set l v st).

  Definition src_interp_as {V} (l: Lens.t state_src V) (VI: V -> iProp) :=
    (∃ SI, (inv N_state_src (∃ st, St_src st ** SI st)) ** ⌜ViewInterp l SI VI⌝)%I.

  Global Program Instance src_interp_as_persistent {V} (l: Lens.t state_src V) (VI: V -> iProp): Persistent (src_interp_as l VI).

  Global Program Instance src_interp_as_acc A E {V} (l: Lens.t state_src V) (VI: V -> iProp):
    IntoAcc
      (src_interp_as l VI)
      (↑N_state_src ⊆ E) True
      (FUpd A E (E ∖ E_state_src)) (FUpd A (E ∖ E_state_src) E) (fun (st: state_src) => ∃ vw, Vw_src st l vw ** VI vw)%I (fun (st: state_src) => ∃ vw, Vw_src st l vw ** VI vw)%I (fun _ => None).
  Next Obligation.
  Proof.
    iIntros "[% [INV %]] _".
    iInv "INV" as "[% [ST INTERP]]" "K". iModIntro.
    iPoseProof (view_interp with "INTERP") as "[INTERP SET]".
    iExists _. iSplitL "ST INTERP".
    { iFrame. iExists _. iFrame.
      unfold Vw_src. iEval (rewrite Lens.set_view). auto.
    }
    iIntros "[% [ST INTERP]]".
    iPoseProof ("SET" with "INTERP") as "INTERP".
    iApply ("K" with "[ST INTERP]").
    iExists _. iFrame.
  Qed.

  Lemma src_interp_as_id A E (SI: state_src -> iProp)
        (IN: InvIn (∃ st, St_src st ** SI st)):
    (∃ st, St_src st ** SI st) ⊢ FUpd A E E (src_interp_as Lens.id (SI)).
  Proof.
    iIntros "H". iPoseProof (FUpd_alloc with "H") as "> H".
    iModIntro. iExists _. iSplit; eauto. iPureIntro. typeclasses eauto.
  Qed.

  Lemma src_interp_as_compose A B
        {la: Lens.t state_src A}
        {lb: Lens.t A B}
        (SA: A -> iProp)
        (SB: B -> iProp)
        `{VAB: ViewInterp _ _ lb SA SB}
    :
    src_interp_as la SA ⊢ src_interp_as (Lens.compose la lb) SB.
  Proof.
    iIntros "[% [H %]]". iExists _. iSplit; [eauto|].
    iPureIntro. typeclasses eauto.
  Qed.



  Definition St_tgt (st_tgt: state_tgt): iProp :=
    OwnM (Auth.white (Excl.just (Some st_tgt): @Excl.t (option state_tgt)): stateTgtRA state_tgt).

  Definition Vw_tgt (st: state_tgt) {V} (l : Lens.t state_tgt V) (v : V) : iProp :=
    St_tgt (Lens.set l v st).

  Definition tgt_interp_as {V} (l: Lens.t state_tgt V) (VI: V -> iProp) :=
    (∃ SI, (inv N_state_tgt (∃ st, St_tgt st ** SI st)) ** ⌜ViewInterp l SI VI⌝)%I.

  Global Program Instance tgt_interp_as_persistent {V} (l: Lens.t state_tgt V) (VI: V -> iProp): Persistent (tgt_interp_as l VI).

  Global Program Instance tgt_interp_as_acc A E {V} (l: Lens.t state_tgt V) (VI: V -> iProp):
    IntoAcc
      (tgt_interp_as l VI)
      (↑N_state_tgt ⊆ E) True
      (FUpd A E (E ∖ E_state_tgt)) (FUpd A (E ∖ E_state_tgt) E) (fun (st: state_tgt) => ∃ vw, Vw_tgt st l vw ** VI vw)%I (fun (st: state_tgt) => ∃ vw, Vw_tgt st l vw ** VI vw)%I (fun _ => None).
  Next Obligation.
  Proof.
    iIntros "[% [INV %]] _".
    iInv "INV" as "[% [ST INTERP]]" "K". iModIntro.
    iPoseProof (view_interp with "INTERP") as "[INTERP SET]".
    iExists _. iSplitL "ST INTERP".
    { iFrame. iExists _. iFrame.
      unfold Vw_tgt. iEval (rewrite Lens.set_view). auto.
    }
    iIntros "[% [ST INTERP]]".
    iPoseProof ("SET" with "INTERP") as "INTERP".
    iApply ("K" with "[ST INTERP]").
    iExists _. iFrame.
  Qed.

  Lemma tgt_interp_as_id A E (SI: state_tgt -> iProp)
        (IN: InvIn (∃ st, St_tgt st ** SI st)):
    (∃ st, St_tgt st ** SI st) ⊢ FUpd A E E (tgt_interp_as Lens.id (SI)).
  Proof.
    iIntros "H". iPoseProof (FUpd_alloc with "H") as "> H".
    iModIntro. iExists _. iSplit; eauto. iPureIntro. typeclasses eauto.
  Qed.

  Lemma tgt_interp_as_compose A B
        {la: Lens.t state_tgt A}
        {lb: Lens.t A B}
        (SA: A -> iProp)
        (SB: B -> iProp)
        `{VAB: ViewInterp _ _ lb SA SB}
    :
    tgt_interp_as la SA ⊢ tgt_interp_as (Lens.compose la lb) SB.
  Proof.
    iIntros "[% [H %]]". iExists _. iSplit; [eauto|].
    iPureIntro. typeclasses eauto.
  Qed.

End STATE.
