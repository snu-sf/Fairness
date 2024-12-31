From sflib Require Import sflib.
(* Port of https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/ghost_map.v into Lilo style iProp *)
(** A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From Fairness Require Import IPM PCM IProp IPropAux.
From Fairness Require Import MonotoneRA.
From Fairness Require Import agree cmra lib.gmap_view.
From Fairness Require Import TemporalLogic.

From Fairness Require Export dfrac.

From iris.prelude Require Import prelude options.

Local Open Scope iris_algebra_scope.

Definition ghost_mapURA (K V : Type) `{Countable K} : URA.t := @FiniteMap.t (of_RA.t (of_IrisRA.t (gmap_viewR K (agreeR V)))).

Section definitions.
  Context {K V : Type} `{Countable K}.
  Context `{GHOSTMAPURA : @GRA.inG (ghost_mapURA K V) Σ}.

  Definition ghost_map_auth_ra
    (γ : nat) (q : Qp) (m : gmap K V) : ghost_mapURA K V :=
    FiniteMap.singleton γ
      (of_RA.to_ura (of_IrisRA.to_ra (gmap_view_auth (V:=agreeR V) (DfracOwn q) (to_agree <$> m)))).
  Definition ghost_map_auth
      (γ : nat) (q : Qp) (m : gmap K V) : iProp :=
    OwnM (ghost_map_auth_ra γ q m).

  Definition ghost_map_elem_ra
    (γ : nat) (k : K) (dq : dfrac) (v : V) : ghost_mapURA K V :=
    FiniteMap.singleton γ
      (of_RA.to_ura (of_IrisRA.to_ra (gmap_view_frag (V:=agreeR V) k dq (to_agree v))) : of_RA.t (of_IrisRA.t (gmap_viewR K (agreeR V)))).
  Definition ghost_map_elem
      (γ : nat) (k : K) (dq : dfrac) (v : V) : iProp :=
    OwnM (ghost_map_elem_ra γ k dq v).
End definitions.

(* bi_scope, not iris_algebra scope cause I actually wanto to use this. *)
Notation "k ↪[ γ ]{ dq } v" := (ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq at level 50, format "k  ↪[ γ ]{ dq }  v") : bi_scope.
Notation "k ↪[ γ ]{# q } v" := (k ↪[γ]{DfracOwn q} v)%I
  (at level 20, γ at level 50, q at level 50, format "k  ↪[ γ ]{# q }  v") : bi_scope.
Notation "k ↪[ γ ] v" := (k ↪[γ]{#1} v)%I
  (at level 20, γ at level 50, format "k  ↪[ γ ]  v") : bi_scope.
Notation "k ↪[ γ ]□ v" := (k ↪[γ]{DfracDiscarded} v)%I
  (at level 20, γ at level 50) : bi_scope.

Local Ltac unseal :=
  repeat unfold ghost_map_auth_ra,ghost_map_auth,ghost_map_elem,ghost_map_elem_ra,ghost_mapURA.

Section lemmas.
  Context `{Σ : GRA.t}.
  Context `{Countable K, GHOSTMAPURA : @GRA.inG (ghost_mapURA K V) Σ}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  (** * Lemmas about the map elements *)
  Global Instance ghost_map_elem_persistent k γ v : Persistent (k ↪[γ]□ v).
  Proof.
    unfold Persistent. unseal.
    iIntros "H".
    iDestruct (own_persistent with "H") as "H".
    rewrite FiniteMap.singleton_core.
    rewrite of_RA.to_ura_core. rewrite of_IrisRA.to_ra_pcore.
    des_ifs.
    rewrite Fairness.cmra.core_id in Heq0; last first.
    { apply _. }
    by injection Heq0 as ->.
  Qed.

  Lemma ghost_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    iIntros "Helem". unseal.
    iDestruct (OwnM_valid with "Helem") as %?%FiniteMap.singleton_wf%of_RA.to_ura_wf%of_IrisRA.to_ra_wf%gmap_view_frag_valid.
    naive_solver.
  Qed.
  Lemma ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜(✓ (dq1 ⋅ dq2))%ia ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    iDestruct (OwnM_valid with "H") as %[? Hag]%FiniteMap.singleton_wf%of_RA.to_ura_wf%of_IrisRA.to_ra_wf%gmap_view_frag_op_valid.
    iPureIntro. split; first done.
    rewrite -to_agree_op_valid. done.
  Qed.
  Lemma ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Lemma ghost_map_elem_combine k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_map_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl".
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    rewrite -gmap_view_frag_op.
    (* TODO: WHY???? *)
    unfold cmra_op,cmra_car. simpl.
    rewrite agree_idemp. eauto with iFrame.
  Qed.

  Lemma ghost_map_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma ghost_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_map_elem_frac_ne. apply: exclusive_l. Qed.

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof.
    unseal. iApply OwnM_Upd.
    apply FiniteMap.singleton_updatable, of_RA.to_ura_updatable,
      of_IrisRA.to_ra_updatable.
    apply gmap_view_frag_persist.
  Qed.

  (** Recover fractional ownership for read-only element. *)

  (** * Lemmas about [ghost_map_auth] *)
  Lemma ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    iDestruct (@OwnM_unit _ _ GHOSTMAPURA) as "H".

    iMod (OwnM_Upd_set with "H") as "[%RES [%HGmap Gmap]]".
    { apply FiniteMap.singleton_alloc.
      instantiate (1 := of_RA.to_ura (of_IrisRA.to_ra (gmap_view_auth (V:=agreeR V) (DfracOwn 1) ∅)): of_RA.t (of_IrisRA.t (gmap_viewR K (agreeR V)))).
      apply of_RA.to_ura_wf, of_IrisRA.to_ra_wf,gmap_view_auth_dfrac_valid.
      done.
    }
    simpl in *. destruct HGmap as [γ ->].
    iModIntro. iExists γ. unseal.
    rewrite fmap_empty. iFrame.
  Qed.


  Lemma ghost_map_auth_valid γ q m : ghost_map_auth γ q m -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (OwnM_valid with "Hauth") as %?%FiniteMap.singleton_wf%of_RA.to_ura_wf%of_IrisRA.to_ra_wf%gmap_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma ghost_map_auth_valid_2 γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    iDestruct (OwnM_valid with "H") as
      %[? Hag]
        %FiniteMap.singleton_wf
        %of_RA.to_ura_wf
        %of_IrisRA.to_ra_wf
        %gmap_view_auth_dfrac_op_valid.
    iPureIntro. split; first done.
    naive_solver.
  Qed.
  Lemma ghost_map_auth_agree γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma ghost_map_lookup {γ q m k dq v} :
    ghost_map_auth γ q m -∗ k ↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iCombine "Hauth Hel" as "H".
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    iDestruct (OwnM_valid with "H") as
      %(av' & _ & _ & Hav' & _ & Hincl)
        %FiniteMap.singleton_wf
        %of_RA.to_ura_wf
        %of_IrisRA.to_ra_wf
        %gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    apply to_agree_included in Hincl. by rewrite Hincl.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ] v.
  Proof.
    unseal. intros Hm. rewrite -OwnM_op.
    iApply Own_Upd.
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    apply GRA.embed_updatable, FiniteMap.singleton_updatable,
      of_RA.to_ura_updatable, of_IrisRA.to_ra_updatable.

    rewrite fmap_insert.
    apply: gmap_view_alloc; [|done|apply to_agree_valid].
    rewrite lookup_fmap. rewrite Hm. done.
  Qed.
  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_delete {γ m k v} :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (delete k m).
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -OwnM_op.
    iApply Own_Upd.
    rewrite FiniteMap.singleton_add.
    rewrite of_RA.to_ura_add.
    rewrite of_IrisRA.to_ra_add.
    apply GRA.embed_updatable, FiniteMap.singleton_updatable,
      of_RA.to_ura_updatable, of_IrisRA.to_ra_updatable.
    rewrite fmap_delete. apply: gmap_view_delete.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (<[k := w]> m) ∗ k ↪[γ] w.
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -!OwnM_op.
    iApply Own_Upd.

    rewrite !FiniteMap.singleton_add.
    rewrite !of_RA.to_ura_add.
    rewrite !of_IrisRA.to_ra_add.
    apply GRA.embed_updatable, FiniteMap.singleton_updatable,
      of_RA.to_ura_updatable, of_IrisRA.to_ra_updatable.

    rewrite fmap_insert. apply: gmap_view_replace. apply to_agree_valid.
  Qed.

End lemmas.

Section SPROP.

Context {K V : Type} `{Countable K}.
Context {STT : StateTypes}.
Context `{sub : @SRA.subG Γ Σ}.
Context {TLRASs : TLRAs_small STT Γ}.
Context {TLRAS : TLRAs STT Γ Σ}.

Context `{HasGhostMap : @GRA.inG (ghost_mapURA K V) Γ}.

  Definition syn_ghost_map_auth {n} γ q m : sProp n := (➢(ghost_map_auth_ra γ q m))%S.
  Definition syn_ghost_map_elem {n} k γ dq v : sProp n := (➢(ghost_map_elem_ra k γ dq v))%S.

  Lemma red_syn_ghost_map_auth n γ q m :
    ⟦syn_ghost_map_auth γ q m, n⟧ = ghost_map_auth γ q m.
  Proof.
    unfold syn_ghost_map_auth. red_tl. ss.
  Qed.

  Lemma red_syn_ghost_map_elem n k γ dq v:
    ⟦syn_ghost_map_elem k γ dq v, n⟧ = ghost_map_elem k γ dq v.
  Proof.
    unfold syn_ghost_map_elem. red_tl. ss.
  Qed.

End SPROP.

Ltac red_tl_ghost_map := (
  try rewrite ! red_syn_ghost_map_auth;
  try rewrite ! red_syn_ghost_map_elem
).

Notation "k ↪[ γ ]{ dq } v" := (syn_ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq at level 50, format "k  ↪[ γ ]{ dq }  v") : sProp_scope.
Notation "k ↪[ γ ]{# q } v" := (k ↪[γ]{DfracOwn q} v)%S
  (at level 20, γ at level 50, q at level 50, format "k  ↪[ γ ]{# q }  v") : sProp_scope.
Notation "k ↪[ γ ] v" := (k ↪[γ]{#1} v)%S
  (at level 20, γ at level 50, format "k  ↪[ γ ]  v") : sProp_scope.
Notation "k ↪[ γ ]□ v" := (k ↪[γ]{DfracDiscarded} v)%S
  (at level 20, γ at level 50) : sProp_scope.
