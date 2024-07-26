From sflib Require Import sflib.
From Fairness Require Import Any PCM IProp IPM IPropAux.
From Fairness Require Import TemporalLogic.


Module Excls.

  Definition t (A : Type) : ucmra := (nat ==> (Excl.t A))%ra.

  Section RA.

    Context `{Σ : GRA.t}.
    (* Map from nat to Auth Excl A. *)
    Context `{HasExcls : @GRA.inG (t A) Σ}.

    Definition ex_ra (r : nat) a : t A :=
      (maps_to_res r (Some a : Excl.t A)).

    Definition ex (r : nat) a : iProp := OwnM (ex_ra r a).

    Definition rest_ra {D : nat -> Prop} (DEC : forall i, Decision (D i)) a :=
      ((fun k => if (DEC k)
              then ε
              else ((Some a : Excl.t A)))
        : t A).

    Definition rest {D : nat -> Prop} (DEC : forall i, Decision (D i)) a : iProp :=
      OwnM (rest_ra DEC a).

    (** Properties. *)

    Lemma exclusive r (t1 t2 : A) :
      ⊢ ex r t1 -∗ ex r t2 -∗ False.
    Proof.
      iIntros "A B". iCombine "A B" as "C". iPoseProof (OwnM_valid with "C") as "%WF".
      iPureIntro. unfold ex_ra in WF. setoid_rewrite maps_to_res_add in WF.
      unfold maps_to_res in WF. ur in WF. specialize (WF r). des_ifs. ur in WF. auto.
    Qed.

    Lemma alloc_gen
          {D1 D2 : nat -> Prop}
          (DEC1 : forall a, Decision (D1 a))
          (DEC2 : forall a, Decision (D2 a))
          (SUB : forall n, match DEC1 n, DEC2 n with
                      | left _, right _ => False
                      | _, _ => True
                      end)
          a
      :
      ⊢ (rest DEC1 a) -∗
        |==> ((rest DEC2 a)
                ∗ (OwnM ((fun k => if (DEC1 k)
                                then ε
                                else if (DEC2 k)
                                     then (Some a : Excl.t A)
                                     else ε
                         ) : t A))).
    Proof.
      iIntros "A".
      assert (URA.updatable
                ((λ k : nat, if DEC1 k
                           then ε
                           else (Some a : Excl.t A)) : t A)
                (((λ k : nat, if DEC2 k
                            then ε
                            else (Some a : Excl.t A)) : t A)
                   ⋅
                   ((fun k => if (DEC1 k)
                           then ε
                           else if (DEC2 k)
                                then (Some a : Excl.t A)
                                else ε) : t A))).
      { setoid_rewrite unfold_pointwise_add. apply pointwise_updatable. i. specialize (SUB a0). des_ifs.
        - rewrite URA.unit_id. reflexivity.
        - rewrite URA.unit_idl. reflexivity.
        - rewrite URA.unit_id. reflexivity.
      }
      iMod (OwnM_Upd with "A") as "[A B]". eauto.
      iModIntro. iFrame.
    Qed.

    Lemma alloc_one
          {D1 D2 : nat -> Prop}
          (DEC1 : forall a, Decision (D1 a))
          (DEC2 : forall a, Decision (D2 a))
          a0
          (ONE : exists m, forall n,
              (n <> m -> match DEC1 n, DEC2 n with | left _, left _ | right _, right _ => True | _, _ => False end)
              /\ (match DEC1 m, DEC2 m with | right _, left _ => True | _, _ => False end))
      :
      ⊢ (rest DEC1 a0) -∗ |==> ((rest DEC2 a0) ∗ ∃ r, ex r a0).
    Proof.
      iIntros "A". des.
      iMod (alloc_gen with "A") as "[A G]".
      2:{ iFrame. assert (
            ((λ k : nat,
                 if DEC1 k then ε else if DEC2 k then (Some a0 : Excl.t A) else ε) : t A)
            =
              (ex_ra m a0)).
          { unfold ex_ra. unfold maps_to_res. extensionalities k.
            specialize (ONE k). des. des_ifs.
          }
          rewrite H. iExists m. iModIntro. iFrame.
      }
      i. specialize (ONE n). des. des_ifs. apply ONE. intros EQ. subst. clarify.
    Qed.

    Definition rest_gt a : iProp := (∃ U, rest (gt_dec U) a).

    Lemma alloc_gt a0 :
      ⊢ rest_gt a0 -∗ |==> (rest_gt a0 ∗ ∃ r, ex r a0).
    Proof.
      iIntros "[%U A]".
      iMod (alloc_one (gt_dec U) (gt_dec (S U)) with "A") as "(A & RES)".
      2:{ iModIntro. iSplitL "A". iExists _. iFrame. iFrame. }
      exists U. i. split.
      { i. des_ifs; try lia. }
      { des_ifs; try lia. }
    Qed.

  End RA.

End Excls.

Module SExcls.

  Section SPROP.

    Context {STT : StateTypes}.
    Context `{sub : @SRA.subG Γ Σ}.
    Context {TLRASs : TLRAs_small STT Γ}.
    Context {TLRAS : TLRAs STT Γ Σ}.

    Context `{HasExcls : @GRA.inG (Excls.t A) Γ}.

    Import Excls.

    Definition s_ex {n} (r : nat) a : sProp n := (➢(ex_ra r a))%S.

    Lemma red_s_ex n r a :
      ⟦s_ex r a, n⟧ = ex r a.
    Proof.
      unfold s_ex. red_tl. ss.
    Qed.

    Definition s_rest {n} {D : nat -> Prop} (DEC : forall i, Decision (D i)) a : sProp n :=
      (➢ (rest_ra DEC a))%S.

    Lemma red_s_rest n D (DEC : forall i, Decision (D i)) a :
      ⟦s_rest DEC a, n⟧ = rest DEC a.
    Proof.
      unfold s_rest. red_tl. ss.
    Qed.

  End SPROP.

End SExcls.

Ltac red_tl_excls := (try rewrite ! @SExcls.red_s_ex;
                      try rewrite ! @SExcls.red_s_rest
                     ).

Notation "'EX' γ a" := (Excls.ex γ a) (at level 90, γ, a at level 1) : bi_scope.
Notation "'EX' γ a" := (SExcls.s_ex γ a) (at level 90, γ, a at level 1) : sProp_scope.
