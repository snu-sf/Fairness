From sflib Require Import sflib.
Require Import Program.
From Fairness Require Import PCM IPM.
From Fairness Require Import Axioms.

From iris.algebra Require Import cmra lib.excl_auth functions.
Set Implicit Arguments.

Section AUX.
  Fixpoint sep_conjs `{Σ: GRA.t} (Ps : nat -> iProp Σ) (n : nat) : iProp Σ :=
    match n with
    | O => True
    | S m => (sep_conjs Ps m) ∗ (Ps m)
    end.
End AUX.

Definition maps_to {Σ} {A: Type} {M: ucmra} `{ING: @GRA.inG (A -d> M) Σ}
           (a: A) (m: M): iProp Σ :=
  OwnM (maps_to_res a m).

Section UPD.
  Variable A: Type.
  Context `{IN: @GRA.inG (excl_authUR $ leibnizO A) Σ}.

  Lemma black_white_update (a0 a' a1 : A)
    :
    (OwnM (●E (a0 : leibnizO A)))
      -∗
      (OwnM (◯E (a' : leibnizO A)))
      -∗
      #=> (OwnM (●E (a1 : leibnizO A))) ∗ OwnM (◯E (a1 : leibnizO A)).
  Proof.
    rewrite bi.wand_curry -!OwnM_op.
    apply bi.entails_wand, OwnM_Upd, excl_auth_update.
  Qed.

  Lemma black_white_equal (a a' : A)
    :
    (OwnM (●E (a : leibnizO A)))
      -∗
      (OwnM (◯E (a' : leibnizO A)))
      -∗
      ⌜a = a'⌝.
  Proof.
    iIntros "H0 H1". by iCombine "H0 H1" gives %?%excl_auth_agree_L.
  Qed.

  Lemma white_white_excl a a'
    :
    (OwnM (excl_auth_frag a))
      -∗
      (OwnM (excl_auth_frag a' ))
      -∗
      ⌜False⌝.
  Proof.
    iIntros "H0 H1". by iCombine "H0 H1" gives %?%excl_auth_frag_op_valid.
  Qed.

End UPD.

Section OWNS.

  Variable (Id: Type).
  Context `{R: ucmra}.
  Context `{IN1: @GRA.inG R Σ}.
  Context `{IN2: @GRA.inG (Id -d> R) Σ}.
  Notation iProp := (iProp Σ) (only parsing).

  Definition OwnMs (s: Id -> Prop) (u: R): iProp :=
    OwnM ((λ i, if (excluded_middle_informative (s i))
                then u else ε) : _ -d> _ ).

  Lemma OwnMs_impl (s0 s1: Id -> Prop) u
        (IMPL: forall i (IN: s0 i), s1 i)
    :
    OwnMs s1 u ⊢ OwnMs s0 u.
  Proof.
    apply OwnM_extends, discrete_fun_included_spec_2.
    i. des_ifs. exfalso. eauto.
  Qed.

  Lemma OwnMs_empty s u
        P (EMPTY: forall i, ~ s i)
    :
    P ⊢ OwnMs s u.
  Proof.
    rewrite (OwnM_unit P).
    apply OwnM_extends, discrete_fun_included_spec_2.
    i. des_ifs. exfalso. by eapply EMPTY.
  Qed.

  Lemma OwnMs_fold (s0 s1: Id -> Prop) i u
        (IMPL: forall j (IN: s0 j), s1 j \/ j = i)
    :
    OwnMs s1 u ∗ maps_to i u
      ⊢
      OwnMs s0 u.
  Proof.
    rewrite -OwnM_op.
    apply OwnM_extends, discrete_fun_included_spec_2.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; ss; rewrite ?right_id ?left_id //=.
    hexploit IMPL; eauto. i. des; ss. subst.
    by rewrite discrete_fun_lookup_singleton.
  Qed.

  Definition OwnMs_unfold (s0 s1: Id -> Prop) i u
             (IMPL: forall j (IN: s0 j \/ j = i), s1 j)
             (NIN: ~ s0 i)
    :
    OwnMs s1 u
      ⊢
      OwnMs s0 u ∗ maps_to i u.
  Proof.
    rewrite -OwnM_op.
    apply OwnM_extends, discrete_fun_included_spec_2=> a.
    rewrite !discrete_fun_op maps_to_res_eq.
    des_ifs; ss; rewrite ?right_id ?left_id //=.
    all: naive_solver.
  Qed.

  Definition OwnMs_combine (s0 s1: Id -> Prop) u
    :
    OwnMs s0 u ∗ OwnMs s1 u
      ⊢
      OwnMs (λ i, (s0 i ∨ s1 i)%type) u.
  Proof.
    rewrite -OwnM_op.
    apply OwnM_extends, discrete_fun_included_spec_2.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; des; ss; rewrite ?right_id ?left_id //=.
  Qed.

  Definition OwnMs_split (s0 s1: Id -> Prop) u
             (DISJOINT: forall i (IN0: s0 i) (IN1: s1 i), False)
    :
    OwnMs (λ i, (s0 i ∨ s1 i)%type ) u
      ⊢
      OwnMs s0 u ∗ OwnMs s1 u.
  Proof.
    rewrite -OwnM_op.
    apply OwnM_extends, discrete_fun_included_spec_2.
    i. rewrite discrete_fun_lookup_op.
    des_ifs; ss; rewrite ?right_id ?left_id //=.
    all: naive_solver.
  Qed.

End OWNS.
