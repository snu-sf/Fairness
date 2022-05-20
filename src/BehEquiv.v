From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Export ITreeNotations.

Require Import Coq.Classes.RelationClasses.

From Fairness Require Import ITreeLib.
From Fairness Require Import FairBeh.
From Fairness Require Import SelectBeh.

From Fairness Require Import Axioms.

Set Implicit Arguments.

Section EXTRACT.

  Context {Ident: ID}.

  (** match between raw_tr and tr *)
  Variant _raw_spin
          (raw_spin: forall (R: Type), RawTr.t -> Prop)
          R
    :
    (@RawTr.t _ R) -> Prop :=
    | raw_spin_silent
        (silent: silentE) tl
        (TL: raw_spin _ tl)
      :
      _raw_spin raw_spin (RawTr.cons (inl silent) tl)
  .

  Definition raw_spin: forall (R: Type), RawTr.t -> Prop := paco2 _raw_spin bot2.

  Lemma raw_spin_mon: monotone2 _raw_spin.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.


  Inductive _extract_tr
            (extract_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop)
            R
    :
    (@RawTr.t _ R) -> Tr.t -> Prop :=
  | extract_tr_done
      retv
    :
    _extract_tr extract_tr (RawTr.done retv) (Tr.done retv)
  | extract_tr_spin
      raw
      (RSPIN: raw_spin raw)
    :
    _extract_tr extract_tr raw (Tr.spin)
  | extract_tr_ub
    :
    _extract_tr extract_tr (RawTr.ub) (Tr.ub)
  | extract_tr_nb
    :
    _extract_tr extract_tr (RawTr.nb) (Tr.nb)
  | extract_tr_obs
      (obs: obsE) raw_tl tr_tl
      (TL: extract_tr _ raw_tl tr_tl)
    :
    _extract_tr extract_tr (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl)
  | extract_tr_silent
      (silent: silentE) raw_tl tr_tl
      (TL: _extract_tr extract_tr raw_tl tr_tl)
    :
    _extract_tr extract_tr (RawTr.cons (inl silent) raw_tl) tr_tl
  .

  Definition extract_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop := paco3 _extract_tr bot3.

  Lemma extract_tr_ind
        (extract_tr : forall R : Type, RawTr.t -> Tr.t -> Prop) (R : Type) (P: RawTr.t -> Tr.t -> Prop)
        (DONE: forall retv : R, P (RawTr.done retv) (Tr.done retv))
        (SPIN: forall (raw : RawTr.t) (RSPIN: raw_spin raw), P raw Tr.spin)
        (UB: P RawTr.ub Tr.ub)
        (NB: P RawTr.nb Tr.nb)
        (OBS: forall (obs : obsE) (raw_tl : RawTr.t) (tr_tl : Tr.t) (TL: extract_tr R raw_tl tr_tl),
            P (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl))
        (SILENT: forall (silent : silentE) (raw_tl : RawTr.t) (tr_tl : Tr.t)
                   (STEP: _extract_tr extract_tr raw_tl tr_tl) (IH: P raw_tl tr_tl),
            P (RawTr.cons (inl silent) raw_tl) tr_tl)
    :
    forall raw_tr tr, (_extract_tr extract_tr raw_tr tr) -> P raw_tr tr.
  Proof.
    fix IH 3; i.
    inv H; eauto.
  Qed.

  Lemma extract_tr_mon: monotone3 _extract_tr.
  Proof.
    ii. induction IN using extract_tr_ind; econs; eauto.
  Qed.

  Local Hint Constructors _raw_spin.
  Local Hint Unfold raw_spin.
  Local Hint Resolve raw_spin_mon: paco.
  Local Hint Constructors _extract_tr.
  Local Hint Unfold extract_tr.
  Local Hint Resolve extract_tr_mon: paco.

  Lemma extract_tr_ind2
        (R : Type) (P: RawTr.t -> Tr.t -> Prop)
        (DONE: forall retv : R, P (RawTr.done retv) (Tr.done retv))
        (SPIN: forall (raw : RawTr.t) (RSPIN: raw_spin raw), P raw Tr.spin)
        (UB: P RawTr.ub Tr.ub)
        (NB: P RawTr.nb Tr.nb)
        (OBS: forall (obs : obsE) (raw_tl : RawTr.t) (tr_tl : Tr.t) (TL: extract_tr raw_tl tr_tl),
            P (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl))
        (SILENT: forall (silent : silentE) (raw_tl : RawTr.t) (tr_tl : Tr.t)
                   (STEP: extract_tr raw_tl tr_tl) (IH: P raw_tl tr_tl),
            P (RawTr.cons (inl silent) raw_tl) tr_tl)
    :
    forall raw_tr tr, (extract_tr raw_tr tr) -> P raw_tr tr.
  Proof.
    i. punfold H. induction H using extract_tr_ind; eauto.
    pclearbot. eapply OBS. eauto.
  Qed.

  Variant extract_tr_indC
          (extract_tr: forall (R: Type), RawTr.t -> Tr.t -> Prop)
          R
    :
    (@RawTr.t _ R) -> Tr.t -> Prop :=
    | extract_tr_indC_done
        retv
      :
      extract_tr_indC extract_tr (RawTr.done retv) (Tr.done retv)
    | extract_tr_indC_spin
        raw
        (RSPIN: raw_spin raw)
      :
      extract_tr_indC extract_tr raw (Tr.spin)
    | extract_tr_indC_ub
      :
      extract_tr_indC extract_tr (RawTr.ub) (Tr.ub)
    | extract_tr_indC_nb
      :
      extract_tr_indC extract_tr (RawTr.nb) (Tr.nb)
    | extract_tr_indC_obs
        (obs: obsE) raw_tl tr_tl
        (TL: extract_tr _ raw_tl tr_tl)
      :
      extract_tr_indC extract_tr (RawTr.cons (inr obs) raw_tl) (Tr.cons obs tr_tl)
    | extract_tr_indC_silent
        (silent: silentE) raw_tl tr_tl
        (TL: extract_tr _ raw_tl tr_tl)
      :
      extract_tr_indC extract_tr (RawTr.cons (inl silent) raw_tl) tr_tl
  .

  Lemma extract_tr_indC_mon: monotone3 extract_tr_indC.
  Proof. ii. inv IN; econs; eauto. Qed.

  Local Hint Resolve extract_tr_indC_mon: paco.

  Lemma extract_tr_indC_wrespectful: wrespectful3 _extract_tr extract_tr_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    { econs; eauto. eapply rclo3_base. eauto. }
    { econs; eauto. eapply extract_tr_mon; eauto. i. eapply rclo3_base. auto. }
  Qed.

  Lemma extract_tr_indC_spec: extract_tr_indC <4= gupaco3 _extract_tr (cpn3 _extract_tr).
  Proof. i. eapply wrespect3_uclo; eauto with paco. eapply extract_tr_indC_wrespectful. Qed.

End EXTRACT.
#[export] Hint Constructors _raw_spin.
#[export] Hint Unfold raw_spin.
#[export] Hint Resolve raw_spin_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
#[export] Hint Constructors _extract_tr.
#[export] Hint Unfold extract_tr.
#[export] Hint Resolve extract_tr_mon: paco.
#[export] Hint Resolve cpn3_wcompat: paco.



Section ExtractTr.

  Context {Ident: ID}.

  Lemma extract_eq_done
        R (tr: @Tr.t R) retv
        (EXTRACT: extract_tr (RawTr.done retv) tr)
    :
    tr = Tr.done retv.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma extract_eq_ub
        R (tr: @Tr.t R)
        (EXTRACT: extract_tr RawTr.ub tr)
    :
    tr = Tr.ub.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.

  Lemma extract_eq_nb
        R (tr: @Tr.t R)
        (EXTRACT: extract_tr RawTr.nb tr)
    :
    tr = Tr.nb.
  Proof.
    punfold EXTRACT. inv EXTRACT; eauto. punfold RSPIN. inv RSPIN.
  Qed.



  (** observer of the raw trace **)
  Inductive observe_raw_first
          R
    :
    (@RawTr.t _ R) -> (prod (option obsE) RawTr.t) -> Prop :=
    | observe_raw_first_done
        retv
      :
      observe_raw_first (RawTr.done retv) (None, (RawTr.done retv))
    | observe_raw_first_ub
      :
      observe_raw_first RawTr.ub (None, RawTr.ub)
    | observe_raw_first_nb
      :
      observe_raw_first RawTr.nb (None, RawTr.nb)
    | observe_raw_first_obs
        (obs: obsE) tl
      :
      observe_raw_first (RawTr.cons (inr obs) tl) (Some obs, tl)
    | observe_raw_first_silent
        (silent: silentE) obs tl tl0
        (STEP: observe_raw_first tl (obs, tl0))
      :
      observe_raw_first (RawTr.cons (inl silent) tl) (obs, tl0)
  .

  Definition observe_raw_prop {R}
             (raw: @RawTr.t _ R)
             (obstl: option (prod (option obsE) RawTr.t)): Prop :=
    match obstl with
    | None => raw_spin raw
    | Some obstl0 => observe_raw_first raw obstl0
    end.

  Lemma inhabited_observe_raw R: inhabited (option (prod (option obsE) (@RawTr.t _ R))).
  Proof.
    econs. exact None.
  Qed.

  Definition observe_raw {R} (raw: (@RawTr.t _ R)): option (prod (option obsE) RawTr.t) :=
    epsilon _ (@inhabited_observe_raw R) (observe_raw_prop raw).


  (** properties **)
  (* helper lemmas *)
  Lemma spin_no_obs
        R (raw: @RawTr.t _ R)
        (SPIN: raw_spin raw)
    :
    forall ev tl, ~ observe_raw_first raw (ev, tl).
  Proof.
    ii. revert SPIN. induction H; i; ss; clarify.
    - punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN.
    - punfold SPIN. inv SPIN.
    - eapply IHobserve_raw_first; clear IHobserve_raw_first.
      punfold SPIN. inv SPIN. pclearbot. auto.
  Qed.

  Lemma no_obs_spin
        R (raw: @RawTr.t _ R)
        (NOOBS: forall ev tl, ~ observe_raw_first raw (ev, tl))
    :
    raw_spin raw.
  Proof.
    revert_until R. pcofix CIH; i. destruct raw.
    - exfalso. eapply NOOBS. econs.
    - exfalso. eapply NOOBS. econs.
    - exfalso. eapply NOOBS. econs.
    - destruct hd as [silent | obs].
      2:{ exfalso. eapply NOOBS. econs. }
      pfold. econs. right. eapply CIH. ii. eapply NOOBS.
      econs 5. eauto.
  Qed.

  Lemma spin_iff_no_obs
        R (raw: @RawTr.t _ R)
    :
    (raw_spin raw) <-> (forall ev tl, ~ observe_raw_first raw (ev, tl)).
  Proof.
    esplits. split; i. eapply spin_no_obs; eauto. eapply no_obs_spin; eauto.
  Qed.

  Lemma observe_raw_first_inj
        R (raw: @RawTr.t _ R) obstl1 obstl2
        (ORP1: observe_raw_first raw obstl1)
        (ORP2: observe_raw_first raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    depgen obstl2. induction ORP1; i.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
    - inv ORP2; eauto.
  Qed.

  Lemma observe_raw_inj
        R (raw: @RawTr.t _ R) obstl1 obstl2
        (ORP1: observe_raw_prop raw obstl1)
        (ORP2: observe_raw_prop raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    destruct obstl1 as [(obs1, tl1) | ]; ss.
    2:{ destruct obstl2 as [(obs2, tl2) | ]; ss.
        rewrite spin_iff_no_obs in ORP1. eapply ORP1 in ORP2. clarify.
    }
    destruct obstl2 as [(obs2, tl2) | ]; ss.
    2:{ rewrite spin_iff_no_obs in ORP2. eapply ORP2 in ORP1. clarify. }
    f_equal. eapply observe_raw_first_inj; eauto.
  Qed.


  Theorem observe_raw_prop_impl_observe_raw
          R (raw: @RawTr.t _ R) obstl
          (ORP: observe_raw_prop raw obstl)
    :
    observe_raw raw = obstl.
  Proof.
    eapply observe_raw_inj. 2: eauto.
    unfold observe_raw, epsilon. eapply Epsilon.epsilon_spec. eauto.
  Qed.

  Lemma observe_raw_prop_false
        R (raw: @RawTr.t _ R) ev tl
    :
    ~ observe_raw_prop raw (Some (None, RawTr.cons ev tl)).
  Proof.
    ii. ss. remember (None, RawTr.cons ev tl) as obstl. revert Heqobstl. revert ev tl. rename H into ORF.
    induction ORF; i; ss. clarify. eapply IHORF. eauto.
  Qed.

  (** observe_raw reductions **)
  Lemma observe_raw_spin
        R (raw: @RawTr.t _ R)
        (SPIN: raw_spin raw)
    :
    observe_raw raw = None.
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss.
  Qed.

  Lemma raw_spin_observe
        R (raw: @RawTr.t _ R)
        (NONE: observe_raw raw = None)
    :
    raw_spin raw.
  Proof.
    eapply spin_iff_no_obs. ii.
    assert (SOME: ~ observe_raw raw = Some (ev, tl)).
    { ii. clarify. }
    eapply SOME. eapply observe_raw_prop_impl_observe_raw. ss.
  Qed.

  Lemma observe_raw_done
        R (retv: R)
    :
    observe_raw (RawTr.done retv) = Some (None, RawTr.done retv).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.

  Lemma observe_raw_ub
        R
    :
    observe_raw (R:=R) (RawTr.ub) = Some (None, RawTr.ub).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.

  Lemma observe_raw_nb
        R
    :
    observe_raw (R:=R) (RawTr.nb) = Some (None, RawTr.nb).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.

  Lemma observe_raw_obs
        R obs (tl: @RawTr.t _ R)
    :
    observe_raw (RawTr.cons (inr obs) tl) = Some (Some obs, tl).
  Proof.
    eapply observe_raw_prop_impl_observe_raw. ss. econs.
  Qed.


  Lemma observe_first_some_inj
        R (raw: @RawTr.t _ R) obstl1 obstl2
        (SOME: observe_raw raw = Some obstl1)
        (ORF: observe_raw_first raw obstl2)
    :
    obstl1 = obstl2.
  Proof.
    assert (A: observe_raw_prop raw (Some obstl2)). ss.
    apply observe_raw_prop_impl_observe_raw in A. rewrite SOME in A. clarify.
  Qed.

  Lemma observe_first_some
        R (raw: @RawTr.t _ R) obstl
        (SOME: observe_raw raw = Some obstl)
    :
    observe_raw_first raw obstl.
  Proof.
    assert (NOTSPIN: ~ raw_spin raw).
    { ii. eapply observe_raw_spin in H. clarify. }
    rewrite spin_iff_no_obs in NOTSPIN.
    assert (TEMP: ~ (forall obstl, ~ observe_raw_first raw obstl)).
    { ii. eapply NOTSPIN. i. eauto. }
    eapply Classical_Pred_Type.not_all_not_ex in TEMP. des.
    replace obstl with n; eauto. symmetry. eapply observe_first_some_inj; eauto.
  Qed.

  Theorem observe_raw_spec
          R (raw: @RawTr.t _ R)
    :
    observe_raw_prop raw (observe_raw raw).
  Proof.
    destruct (observe_raw raw) eqn:EQ.
    - ss. eapply observe_first_some; eauto.
    - ss. eapply raw_spin_observe; eauto.
  Qed.

  Lemma observe_raw_silent
        R (tl: @RawTr.t _ R) silent
    :
    observe_raw (RawTr.cons (inl silent) tl) = observe_raw tl.
  Proof.
    eapply observe_raw_prop_impl_observe_raw. destruct (observe_raw tl) eqn:EQ.
    2:{ ss. pfold. econs. left. eapply raw_spin_observe; eauto. }
    ss. destruct p as [obs tl0]. hexploit observe_first_some; eauto. i.
    econs. auto.
  Qed.



  (** raw trace to normal trace **)
  CoFixpoint raw2tr {R} (raw: @RawTr.t _ R): (@Tr.t R) :=
    match observe_raw raw with
    | None => Tr.spin
    | Some (None, RawTr.done retv) => Tr.done retv
    | Some (None, RawTr.ub) => Tr.ub
    | Some (None, RawTr.nb) => Tr.nb
    | Some (None, RawTr.cons _ _) => Tr.ub
    | Some (Some obs, tl) => Tr.cons obs (raw2tr tl)
    end.

  (** reduction lemmas **)
  Lemma raw2tr_red_done
        R (retv: R)
    :
    (raw2tr (RawTr.done retv)) = (Tr.done retv).
  Proof.
    replace (raw2tr (RawTr.done retv)) with (Tr.ob (raw2tr (RawTr.done retv))).
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_done. ss.
  Qed.

  Lemma raw2tr_red_ub
        R
    :
    (raw2tr (R:=R) RawTr.ub) = Tr.ub.
  Proof.
    replace (raw2tr RawTr.ub) with (Tr.ob (R:=R) (raw2tr RawTr.ub)).
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_ub. ss.
  Qed.

  Lemma raw2tr_red_nb
        R
    :
    (raw2tr (R:=R) RawTr.nb) = Tr.nb.
  Proof.
    replace (raw2tr RawTr.nb) with (Tr.ob (R:=R) (raw2tr RawTr.nb)).
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_nb. ss.
  Qed.

  Lemma raw2tr_red_obs
        R obs tl
    :
    (raw2tr (RawTr.cons (inr obs) tl)) = (Tr.cons (R:=R) obs (raw2tr tl)).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (Tr.ob lhs) end.
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_obs. ss.
  Qed.

  Lemma raw2tr_red_spin
        R (raw: @RawTr.t _ R)
        (SPIN: raw_spin raw)
    :
    (raw2tr raw) = Tr.spin.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (Tr.ob lhs) end.
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_spin; eauto.
  Qed.

  Lemma raw2tr_red_silent
        R silent tl
    :
    (raw2tr (RawTr.cons (inl silent) tl)) = (raw2tr (R:=R) tl).
  Proof.
    match goal with | |- ?lhs = ?rhs => replace lhs with (Tr.ob lhs); [replace rhs with (Tr.ob rhs) |] end.
    2:{ symmetry. apply Tr.ob_eq. }
    2:{ symmetry. apply Tr.ob_eq. }
    ss. rewrite observe_raw_silent. ss.
  Qed.

  Theorem raw2tr_extract
          R (raw: @RawTr.t _ R)
    :
    extract_tr raw (raw2tr raw).
  Proof.
    revert_until R. pcofix CIH. i.
    destruct raw.
    { rewrite raw2tr_red_done. pfold. econs. }
    { rewrite raw2tr_red_ub. pfold. econs. }
    { rewrite raw2tr_red_nb. pfold. econs. }
    destruct hd as [silent | obs].
    2:{ rewrite raw2tr_red_obs. pfold. econs. right. eauto. }
    destruct (observe_raw (RawTr.cons (inl silent) raw)) eqn:EQ.
    2:{ eapply raw_spin_observe in EQ. rewrite raw2tr_red_spin; eauto. }
    rename p into obstl.
    remember (RawTr.cons (inl silent) raw) as raw0. clear Heqraw0. clear silent raw.
    pose (observe_raw_spec) as ORS. specialize (ORS R raw0). rewrite EQ in ORS. ss.
    clear EQ. induction ORS; ss.
    { rewrite raw2tr_red_done. pfold. econs. }
    { rewrite raw2tr_red_ub. pfold. econs. }
    { rewrite raw2tr_red_nb. pfold. econs. }
    { rewrite raw2tr_red_obs. pfold. econs. right. eauto. }
    pfold. econs. punfold IHORS. remember (raw2tr tl) as tr. depgen silent. depgen tl0. revert Heqtr. depgen obs.
    induction IHORS using (@extract_tr_ind); i.
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_done. econs. }
    { exfalso. eapply spin_iff_no_obs in RSPIN. eauto. }
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_ub. econs. }
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_nb. econs. }
    { rewrite raw2tr_red_silent. rewrite raw2tr_red_obs. econs. right. auto. }
    econs 6. rewrite raw2tr_red_silent. eapply IHIHORS; eauto.
    - rewrite raw2tr_red_silent in Heqtr. auto.
    - instantiate (1:=tl0). instantiate (1:=obs). inv ORS. auto.
  Qed.

End ExtractTr.



Section ExtractRaw.

  Context {Ident: ID}.
  Variable wf: WF.

  Definition st_tr_im {R} := ((@state _ R) * (@Tr.t R) * (imap wf))%type.

  (* (** well formed state-trace relation **) *)
  (* Variant _wf_spin *)
  (*         (wf_spin: forall R, (@state _ R) -> Prop) *)
  (*         R *)
  (*   : *)
  (*   (@state _ R) -> Prop := *)
  (*   | wf_spin_tau *)
  (*       itr *)
  (*       (WFS: wf_spin R itr) *)
  (*     : *)
  (*     _wf_spin wf_spin (Tau itr) *)
  (*   | wf_spin_choose *)
  (*       X ktr x *)
  (*       (WFS: wf_spin R (ktr x)) *)
  (*     : *)
  (*     _wf_spin wf_spin (Vis (Choose X) ktr) *)
  (*   | wf_spin_fair *)
  (*       fm ktr *)
  (*       (WFS: wf_spin R (ktr tt)) *)
  (*     : *)
  (*     _wf_spin wf_spin (Vis (Fair fm) ktr) *)
  (*   | wf_spin_ub *)
  (*       ktr *)
  (*     : *)
  (*     _wf_spin wf_spin (Vis Undefined ktr) *)
  (* . *)

  (* Definition wf_spin: forall R, (@state _ R) -> Prop := paco2 _wf_spin bot2. *)

  (* Lemma wf_spin_mon: monotone2 _wf_spin. *)
  (* Proof. *)
  (*   ii. inv IN. all: econs; eauto. *)
  (* Qed. *)

  (* Local Hint Resolve wf_spin_mon: paco. *)

  (* Inductive _wf_tr *)
  (*           (wf_tr: forall R, (@st_tr_im R) -> Prop) *)
  (*           R *)
  (*   : *)
  (*   (@st_tr_im R) -> Prop := *)
  (* | wf_tr_ret *)
  (*     retv *)
  (*   : *)
  (*   _wf_tr wf_tr (Ret retv, Tr.done retv) *)
  (* | wf_tr_obs *)
  (*     fn args rv ktr tr *)
  (*     (WF: wf_tr _ (ktr rv, tr)) *)
  (*   : *)
  (*   _wf_tr wf_tr (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tr) *)
  (* | wf_tr_spin *)
  (*     itr *)
  (*     (WFS: wf_spin itr) *)
  (*   : *)
  (*   _wf_tr wf_tr (itr, Tr.spin) *)
  (* | wf_tr_tau *)
  (*     itr tr *)
  (*     (STEP: _wf_tr wf_tr (itr, tr)) *)
  (*   : *)
  (*   _wf_tr wf_tr (Tau itr, tr) *)
  (* | wf_tr_choose *)
  (*     X ktr x tr *)
  (*     (STEP: _wf_tr wf_tr (ktr x, tr)) *)
  (*   : *)
  (*   _wf_tr wf_tr (Vis (Choose X) ktr, tr) *)
  (* | wf_tr_fair *)
  (*     fm ktr tr *)
  (*     (STEP: _wf_tr wf_tr (ktr tt, tr)) *)
  (*   : *)
  (*   _wf_tr wf_tr (Vis (Fair fm) ktr, tr) *)
  (* | wf_tr_ub *)
  (*     ktr tr *)
  (*   : *)
  (*   _wf_tr wf_tr (Vis Undefined ktr, tr) *)
  (* | wf_tr_nb *)
  (*     itr *)
  (*   : *)
  (*   _wf_tr wf_tr (itr, Tr.nb) *)
  (* . *)

  (* Definition wf_tr: forall R, (@st_tr_im R) -> Prop := paco2 _wf_tr bot2. *)

  (* Lemma wf_tr_ind *)
  (*       (r: forall R, (@st_tr_im R) -> Prop) R (P: (@st_tr_im R) -> Prop) *)
  (*       (RET: forall retv : R, P (Ret retv, Tr.done retv)) *)
  (*       (OBS: forall (fn : nat) (args : list nat) (rv : nat) (ktr : nat -> state) (tr : Tr.t), *)
  (*           r R (ktr rv, tr) -> P (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tr)) *)
  (*       (SPIN: forall itr : state, wf_spin itr -> P (itr, Tr.spin)) *)
  (*       (TAU: forall (itr : state) (tr : Tr.t) (STEP: _wf_tr r (itr, tr)) (IH: P (itr, tr)), P (Tau itr, tr)) *)
  (*       (CHOOSE: forall (X : Type) (ktr : X -> state) (x : X) (tr : Tr.t) (STEP: _wf_tr r (ktr x, tr)) *)
  (*                  (IH: P (ktr x, tr)), P (Vis (Choose X) ktr, tr)) *)
  (*       (FAIR: forall (fm : fmap) (ktr : unit -> state) (tr : Tr.t) (STEP: _wf_tr r (ktr tt, tr)) *)
  (*                (IH: P (ktr tt, tr)), P (Vis (Fair fm) ktr, tr)) *)
  (*       (UB: forall (ktr : void -> itree eventE R) (tr : Tr.t), P (Vis Undefined ktr, tr)) *)
  (*       (NB: forall itr : state, P (itr, Tr.nb)) *)
  (*   : *)
  (*   forall sttr, @_wf_tr r R sttr -> P sttr. *)
  (* Proof. *)
  (*   fix IH 2. i. inv H; eauto. *)
  (* Qed. *)

  (* Lemma wf_tr_mon: monotone2 _wf_tr. *)
  (* Proof. *)
  (*   ii. induction IN using wf_tr_ind; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (*   - econs; eauto. *)
  (* Qed. *)

  (* Local Hint Constructors _wf_tr. *)
  (* Local Hint Unfold wf_tr. *)
  (* Local Hint Resolve wf_tr_mon: paco. *)
  (* Local Hint Resolve cpn2_wcompat: paco. *)

  (* Lemma wf_tr_ind2 *)
  (*       R (P: (@st_tr_im R) -> Prop) *)
  (*       (RET: forall retv : R, P (Ret retv, Tr.done retv)) *)
  (*       (OBS: forall (fn : nat) (args : list nat) (rv : nat) (ktr : nat -> state) (tr : Tr.t), *)
  (*           wf_tr (ktr rv, tr) -> P (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tr)) *)
  (*       (SPIN: forall itr : state, wf_spin itr -> P (itr, Tr.spin)) *)
  (*       (TAU: forall (itr : state) (tr : Tr.t) (STEP: wf_tr (itr, tr)) (IH: P (itr, tr)), P (Tau itr, tr)) *)
  (*       (CHOOSE: forall (X : Type) (ktr : X -> state) (x : X) (tr : Tr.t) (STEP: wf_tr (ktr x, tr)) *)
  (*                  (IH: P (ktr x, tr)), P (Vis (Choose X) ktr, tr)) *)
  (*       (FAIR: forall (fm : fmap) (ktr : unit -> state) (tr : Tr.t) (STEP: wf_tr (ktr tt, tr)) *)
  (*                (IH: P (ktr tt, tr)), P (Vis (Fair fm) ktr, tr)) *)
  (*       (UB: forall (ktr : void -> itree eventE R) (tr : Tr.t), P (Vis Undefined ktr, tr)) *)
  (*       (NB: forall itr : state, P (itr, Tr.nb)) *)
  (*   : *)
  (*   forall sttr, wf_tr sttr -> P sttr. *)
  (* Proof. *)
  (*   i. eapply wf_tr_ind; eauto. *)
  (*   - i. eapply TAU; eauto. pfold. eapply wf_tr_mon; eauto. *)
  (*   - i. eapply CHOOSE; eauto. pfold. eapply wf_tr_mon; eauto. *)
  (*   - i. eapply FAIR; eauto. pfold. eapply wf_tr_mon; eauto. *)
  (*   - punfold H. eapply wf_tr_mon; eauto. i. pclearbot. eauto. *)
  (* Qed. *)

  (* Variant wf_tr_indC *)
  (*           (wf_tr: forall R, (@st_tr_im R) -> Prop) *)
  (*           R *)
  (*   : *)
  (*   (@st_tr_im R) -> Prop := *)
  (* | wf_tr_indC_ret *)
  (*     retv *)
  (*   : *)
  (*   wf_tr_indC wf_tr (Ret retv, Tr.done retv) *)
  (* | wf_tr_indC_obs *)
  (*     fn args rv ktr tr *)
  (*     (WF: wf_tr _ (ktr rv, tr)) *)
  (*   : *)
  (*   wf_tr_indC wf_tr (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tr) *)
  (* | wf_tr_indC_spin *)
  (*     itr *)
  (*     (WFS: wf_spin itr) *)
  (*   : *)
  (*   wf_tr_indC wf_tr (itr, Tr.spin) *)
  (* | wf_tr_indC_tau *)
  (*     itr tr *)
  (*     (STEP: wf_tr _ (itr, tr)) *)
  (*   : *)
  (*   wf_tr_indC wf_tr (Tau itr, tr) *)
  (* | wf_tr_indC_choose *)
  (*     X ktr x tr *)
  (*     (STEP: wf_tr _ (ktr x, tr)) *)
  (*   : *)
  (*   wf_tr_indC wf_tr (Vis (Choose X) ktr, tr) *)
  (* | wf_tr_indC_fair *)
  (*     fm ktr tr *)
  (*     (STEP: wf_tr _ (ktr tt, tr)) *)
  (*   : *)
  (*   wf_tr_indC wf_tr (Vis (Fair fm) ktr, tr) *)
  (* | wf_tr_indC_ub *)
  (*     ktr tr *)
  (*   : *)
  (*   wf_tr_indC wf_tr (Vis Undefined ktr, tr) *)
  (* | wf_tr_indC_nb *)
  (*     itr *)
  (*   : *)
  (*   wf_tr_indC wf_tr (itr, Tr.nb) *)
  (* . *)

  (* Lemma wf_tr_indC_mon: monotone2 wf_tr_indC. *)
  (* Proof. ii. inv IN; econs; eauto. Qed. *)

  (* Local Hint Resolve wf_tr_indC_mon: paco. *)

  (* Lemma wf_tr_indC_wrespectful: wrespectful2 _wf_tr wf_tr_indC. *)
  (* Proof. *)
  (*   econs; eauto with paco. *)
  (*   i. inv PR; eauto. *)
  (*   { econs; eauto. eapply rclo2_base. eauto. } *)
  (*   { econs; eauto. eapply wf_tr_mon; eauto. i. eapply rclo2_base. auto. } *)
  (*   { econs; eauto. eapply wf_tr_mon; eauto. i. eapply rclo2_base. auto. } *)
  (*   { econs; eauto. eapply wf_tr_mon; eauto. i. eapply rclo2_base. auto. } *)
  (* Qed. *)

  (* Lemma wf_tr_indC_spec: wf_tr_indC <3= gupaco2 _wf_tr (cpn2 _wf_tr). *)
  (* Proof. i. eapply wrespect2_uclo; eauto with paco. eapply wf_tr_indC_wrespectful. Qed. *)



  (** observer of the state, needs trace for obs return value information **)
  Inductive observe_state_trace
            R
    :
    (@st_tr_im R) -> (prod (list rawE) (option st_tr_im)) -> Prop :=
  | observe_state_trace_ret
      (retv: R) im
    :
    observe_state_trace (Ret retv, Tr.done retv, im)
                       ([], Some (Ret retv, Tr.done retv, im))
  | observe_state_trace_obs
      fn args ktr rv tl im
    :
    observe_state_trace (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tl, im)
                       ([inr (obsE_syscall fn args rv)], Some (ktr rv, tl, im))
  | observe_state_trace_tau
      itr tr im evs sti
      (NNB: tr <> Tr.nb)
      (SPIN: tr = Tr.spin -> (Beh.diverge_index im itr /\ evs = [] /\ sti = Some (itr, tr, im)))
      (CONT: tr <> Tr.spin -> observe_state_trace (itr, tr, im) (evs, sti))
    :
    observe_state_trace (Tau itr, tr, im)
                       ((inl silentE_tau) :: evs, sti)
  | observe_state_trace_choose
      X ktr x tr im evs sti
      (NNB: tr <> Tr.nb)
      (SPIN: tr = Tr.spin -> (Beh.diverge_index im (ktr x) /\ evs = [] /\ sti = Some (ktr x, tr, im)))
      (CONT: tr <> Tr.spin -> (observe_state_trace (ktr x, tr, im) (evs, sti) /\ Beh.of_state im (ktr x) tr))
    :
    observe_state_trace (Vis (Choose X) ktr, tr, im)
                       ((inl silentE_tau) :: evs, sti)
  | observe_state_trace_fair
      fm ktr tr im evs sti im0
      (NNB: tr <> Tr.nb)
      (SPIN: tr = Tr.spin -> (Beh.diverge_index im0 (ktr tt) /\ evs = [] /\ sti = Some (ktr tt, tr, im0)))
      (CONT: tr <> Tr.spin -> observe_state_trace (ktr tt, tr, im0) (evs, sti))
      (FAIR: fair_update im im0 fm)
    :
    observe_state_trace (Vis (Fair fm) ktr, tr, im)
                       ((inl (silentE_fair fm)) :: evs, sti)
  | observe_state_trace_ub
      ktr tr im
    :
    observe_state_trace (Vis Undefined ktr, tr, im)
                       ([], Some (Vis Undefined ktr, tr, im))
  | observe_state_trace_nb
      itr im
    :
    observe_state_trace (itr, Tr.nb, im)
                       ([], Some (itr, Tr.nb, im))
  .


  Definition observe_state_prop R (sti: @st_tr_im R) (rawsti: (prod (list rawE) (option st_tr_im))): Prop :=
    let '(st, tr, im) := sti in (Beh.of_state im st tr) -> observe_state_trace sti rawsti.
  (* (<<WF: wf_tr sttr>>) -> (observe_state_trace sttr rawst). *)

  Lemma inhabited_observe_state R: inhabited (prod (list rawE) (option (@st_tr_im R))).
  Proof.
    econs. exact ([], None).
  Qed.

  Definition observe_state {R} (sti: @st_tr_im R): (prod (list rawE) (option st_tr_im)) :=
    epsilon _ (@inhabited_observe_state R) (observe_state_prop sti).


  (** properties **)
  Lemma beh_implies_spin
        R (im: imap wf) (st: @state _ R)
        (BEH: Beh.of_state im st Tr.spin)
    :
    Beh.diverge_index im st.
  Proof.
    revert_until R. pcofix CIH; i. remember Tr.spin as tr. revert Heqtr.
    induction BEH using (@of_state_ind2); i; clarify; ss; eauto.
    { eapply paco3_mon; eauto. ss. }
    { pfold. econs. right. eauto. }
    { pfold. econs. right. eauto. }
    { pfold. econs. right. eauto. eauto. }
  Qed.

  Lemma observe_state_trace_exists
        R (st: @state _ R) (tr: Tr.t) (im: imap wf)
        (BEH: Beh.of_state im st tr)
    :
    exists rawsti, observe_state_trace (st, tr, im) rawsti.
  Proof.
    induction BEH using (@of_state_ind2).
    - eexists. econs.
    - punfold H. inv H.
      + pclearbot. eexists. econs; i; ss; eauto.
      + pclearbot. eexists. econs; i; ss; eauto.
      + pclearbot. eexists. econs; i; ss; eauto.
      + pclearbot. eexists. econs; i; ss; eauto.
    - eexists. econs.
    - eexists. econs.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify; ss.
      + eexists. econs 7.
      + destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify; ss.
        * des. eexists. econs; i; ss; clarify. splits; eauto. eapply beh_implies_spin; eauto.
        * des. destruct rawsti. rr in IHBEH. eexists. econs; i; ss; clarify; eauto.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify; ss.
      + eexists. econs 7.
      + destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify; ss.
        * des. eexists. econs; i; ss; clarify. splits; eauto. eapply beh_implies_spin; eauto.
        * des. destruct rawsti. rr in IHBEH. eexists. econs; i; ss; clarify; eauto.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify; ss.
      + eexists. econs 7.
      + destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify; ss.
        * des. eexists. econs; i; ss; clarify. splits; eauto. eapply beh_implies_spin; eauto. eauto.
        * des. destruct rawsti. rr in IHBEH. eexists. econs; i; ss; clarify; eauto.
    - eexists. econs; eauto.
      Unshelve. all: try exact None. all: try exact [].
  Qed.

  Lemma observe_state_exists
        R (st: @state _ R) (tr: Tr.t) (im: imap wf)
    :
    exists rawsti, observe_state_prop (st, tr, im) rawsti.
  Proof.
    destruct (classic (Beh.of_state im st tr)) as [BEH | NBEH].
    - hexploit observe_state_trace_exists; eauto. i. des. eexists. ii. eauto.
    - eexists. ii. clarify.
      Unshelve. exact ([], None).
  Qed.

  (** (state, trace, imap) to raw trace **)
  CoFixpoint raw_spin_trace {R}: RawTr.t :=
    @RawTr.cons _ R (inl silentE_tau) raw_spin_trace.

  CoFixpoint _sti2raw {R} (evs: list rawE) (sti: @st_tr_im R): (@RawTr.t _ R) :=
    match evs with
    | hd :: tl => RawTr.cons hd (_sti2raw tl sti)
    | [] =>
        match observe_state sti with
        | (evs, Some (Ret _, Tr.done retv, _)) => RawTr.app evs (RawTr.done retv)
        | (evs, Some (Vis Undefined _, Tr.spin, _)) => RawTr.app evs raw_spin_trace
        | (evs, Some (Vis Undefined _, _, _)) => RawTr.app evs RawTr.ub
        | (evs, Some (_, Tr.nb, _)) => RawTr.app evs RawTr.nb
        | (hd :: tl, Some sti0) => RawTr.cons hd (_sti2raw tl sti0)
        | (evs, _) => RawTr.app evs RawTr.ub
        end
    end.

  Definition sti2raw {R} (sti: @st_tr_im R): (@RawTr.t _ R) := _sti2raw [] sti.


  (** observe_state reduction lemmas **)
  Lemma observe_state_ret
        R (im: imap wf) (retv: R)
    :
    observe_state (Ret retv, Tr.done retv, im) = ([], Some (Ret retv, Tr.done retv, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsti. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H. eauto.
  Qed.

  Lemma observe_state_obs
        R (im: imap wf) fn args rv tl ktr
        (BEH: Beh.of_state im (ktr rv) tl)
    :
    observe_state (R:=R) (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tl, im) =
      ([inr (obsE_syscall fn args rv)], Some (ktr rv, tl, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsti. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    { pfold. econs. eauto. }
    i. inv H. eapply inj_pair2 in H3. clarify.
  Qed.

  Lemma observe_state_tau
        R (im: imap wf) itr tr
        (BEH: Beh.of_state im (Tau itr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists evs sti, (observe_state_trace (itr, tr, im) (evs, sti)) /\
                 (observe_state (R:=R) (Tau itr, tr, im) = ((inl silentE_tau) :: evs, sti)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto.
  Qed.

  Lemma observe_state_tau_spin
        R (im: imap wf) itr tr
        (BEH: Beh.of_state im (Tau itr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    (Beh.diverge_index im itr) /\
      observe_state (R:=R) (Tau itr, tr, im) = ([inl silentE_tau], Some (itr, tr, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. hexploit SPIN; ss; i. des; clarify.
  Qed.

  Lemma observe_state_choose
        R (im: imap wf) tr X ktr
        (BEH: Beh.of_state im (Vis (Choose X) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists (x: X) evs sti,
      (Beh.of_state im (ktr x) tr) /\
        (observe_state_trace (ktr x, tr, im) (evs, sti)) /\
        (observe_state (R:=R) (Vis (Choose X) ktr, tr, im) = ((inl silentE_tau) :: evs, sti)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; clarify. eapply inj_pair2 in H0. clarify. hexploit CONT; eauto; i. des. esplits; eauto.
  Qed.

  Lemma observe_state_choose_spin
        R (im: imap wf) tr X ktr
        (BEH: Beh.of_state im (Vis (Choose X) ktr) tr)
        (NNB: tr <> Tr.nb)
        (SPIN: tr = Tr.spin)
    :
    exists (x: X),
      (Beh.diverge_index im (ktr x)) /\
        (observe_state (R:=R) (Vis (Choose X) ktr, tr, im) = ([inl silentE_tau], Some (ktr x, tr, im))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; clarify. eapply inj_pair2 in H0. clarify. hexploit SPIN; eauto; i. des. clarify. eauto.
  Qed.

  Lemma observe_state_fair
        R (im: imap wf) tr fm ktr
        (BEH: Beh.of_state im (Vis (Fair fm) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr <> Tr.spin)
    :
    exists (im0: imap wf) evs sti,
      (fair_update im im0 fm) /\
        (observe_state_trace (ktr tt, tr, im0) (evs, sti)) /\
        (observe_state (R:=R) (Vis (Fair fm) ktr, tr, im) = ((inl (silentE_fair fm)) :: evs, sti)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. eapply inj_pair2 in H2. clarify. hexploit CONT; eauto; i. esplits; eauto.
  Qed.

  Lemma observe_state_fair_spin
        R (im: imap wf) tr fm ktr
        (BEH: Beh.of_state im (Vis (Fair fm) ktr) tr)
        (NNB: tr <> Tr.nb)
        (NSPIN: tr = Tr.spin)
    :
    exists (im0: imap wf),
      (fair_update im im0 fm) /\
        (Beh.diverge_index im0 (ktr tt)) /\
        (observe_state (R:=R) (Vis (Fair fm) ktr, tr, im) = ([inl (silentE_fair fm)], Some (ktr tt, tr, im0))).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; ss; eauto. eapply inj_pair2 in H2. clarify. hexploit SPIN; eauto; i. des. clarify. esplits; eauto.
  Qed.

  Lemma observe_state_ub
        R (im: imap wf) tr ktr
    :
    observe_state (R:=R) (Vis Undefined ktr, tr, im) = ([], Some (Vis Undefined ktr, tr, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; eauto. eapply inj_pair2 in H1. clarify.
  Qed.

  Lemma observe_state_nb
        R (im: imap wf) itr
    :
    observe_state (R:=R) (itr, Tr.nb, im) = ([], Some (itr, Tr.nb, im)).
  Proof.
    unfold observe_state, epsilon. unfold Epsilon.epsilon. unfold proj1_sig. des_ifs.
    rename x into rawsttr. clear Heq.
    hexploit (observe_state_exists). intros OSP. eapply o in OSP; clear o.
    unfold observe_state_prop in OSP. hexploit OSP; clear OSP; eauto.
    i. inv H; clarify.
  Qed.

  Lemma observe_state_spin_div
        R (im: imap wf) itr
        (DIV: @Beh.diverge_index _ _ R im itr)
    :
    observe_state_trace (itr, Tr.spin, im) (observe_state (itr, Tr.spin, im)).
  Proof.
    punfold DIV. inv DIV.
    - pclearbot. hexploit observe_state_tau_spin; ss. 2:ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; ss. }
      pfold. econs; eauto. pfold. econs; eauto.
    - pclearbot. hexploit observe_state_choose_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; eauto; ss. }
      pfold. econs; eauto. pfold. econs; eauto.
    - pclearbot. hexploit observe_state_fair_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H1; clear H1. econs; eauto; ss. }
      pfold. econs; eauto. pfold. econs; eauto.
    - rewrite observe_state_ub. econs; eauto.
  Qed.

  Lemma observe_state_spin
        R (im: imap wf) itr
        (BEH: @Beh.of_state _ _ R im itr Tr.spin)
    :
    observe_state_trace (itr, Tr.spin, im) (observe_state (itr, Tr.spin, im)).
  Proof.
    remember Tr.spin as tr. revert Heqtr. induction BEH using @of_state_ind2; i; ss.
    - eapply observe_state_spin_div; eauto.
    - clarify. hexploit observe_state_tau_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; ss. }
      pfold. econs 5. punfold BEH.
    - clarify. hexploit observe_state_choose_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H0; clear H0. econs; ss. i. splits; eauto. }
      pfold. econs 6. punfold BEH.
    - clarify. hexploit observe_state_fair_spin; ss. 2: ss.
      2:{ i. des. setoid_rewrite H1; clear H1. econs; ss; eauto. }
      pfold. econs 7; eauto. punfold BEH.
    - clarify. rewrite observe_state_ub. econs.
  Qed.

  Theorem observe_state_spec
          R (sti: @st_tr_im R)
    :
    observe_state_prop sti (observe_state sti).
  Proof.
    destruct sti as [[st tr] im]. ii. rename H into BEH.
    ides st.
    - punfold BEH. inv BEH.
      + rewrite observe_state_ret. econs.
      + punfold SPIN. inv SPIN.
      + rewrite observe_state_nb. econs.
    - destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
      { rewrite observe_state_nb. econs. }
      destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
      { eapply observe_state_spin; eauto. }
      hexploit observe_state_tau; ss.
      4:{ i; des. setoid_rewrite H0; clear H0. econs; ss. }
      all: eauto.
    - destruct e.
      + destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
        { rewrite observe_state_nb. econs. }
        destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
        { eapply observe_state_spin; eauto. }
        hexploit observe_state_choose; ss.
        4:{ i; des. setoid_rewrite H1; clear H1. econs; ss. i. splits; eauto. }
        all: eauto.
      + destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
        { rewrite observe_state_nb. econs. }
        destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
        { eapply observe_state_spin; eauto. }
        hexploit observe_state_fair; ss.
        4:{ i; des. setoid_rewrite H1; clear H1. econs; ss. all: eauto. }
        all: eauto.
      + destruct (classic (tr = Tr.nb)) as [NB | NNB]; clarify.
        { rewrite observe_state_nb. econs. }
        destruct (classic (tr = Tr.spin)) as [SPIN | NSPIN]; clarify.
        { eapply observe_state_spin; eauto. }
        punfold BEH. inv BEH; ss. eapply inj_pair2 in H3. clarify. pclearbot.
        rewrite observe_state_obs; eauto. econs.
      + rewrite observe_state_ub. econs.
  Qed.


  (** reduction lemmas **)
  Lemma sttr2raw_red_ret
        R (retv: R)
    :
    sttr2raw (Ret retv, Tr.done retv) = RawTr.done retv.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_ret. ss.
  Qed.

  Lemma sttr2raw_red_obs
        R fn args rv tl ktr
        (WF: wf_tr (ktr rv, tl))
    :
    sttr2raw (R:=R) (Vis (Observe fn args) ktr, Tr.cons (obsE_syscall fn args rv) tl) =
      RawTr.cons (inr (obsE_syscall fn args rv)) (sttr2raw (ktr rv, tl)).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_obs; eauto.
  Qed.

  Lemma sttr2raw_red_tau
        R itr tr
        (WF: wf_tr (itr, tr))
        (NNB: tr <> Tr.nb)
    :
    sttr2raw (R:=R) (Tau itr, tr) = RawTr.cons (inl silentE_tau) (sttr2raw (itr, tr)).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_tau; eauto.
  Qed.

  Lemma sttr2raw_red_choose
        R tr X ktr
        (WF: wf_tr (Vis (Choose X) ktr, tr))
        (NNB: tr <> Tr.nb)
    :
    exists x,
      (wf_tr (ktr x, tr)) /\
        (sttr2raw (R:=R) (Vis (Choose X) ktr, tr) = RawTr.cons (inl silentE_tau) (sttr2raw (ktr x, tr))).
  Proof.
    hexploit observe_state_choose; eauto. i. des. exists x. split; eauto.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite H0; eauto.
  Qed.

  Lemma sttr2raw_red_fair
        R tr fm ktr
        (WF: wf_tr (ktr tt, tr))
        (NNB: tr <> Tr.nb)
    :
    sttr2raw (R:=R) (Vis (Fair fm) ktr, tr) =
      RawTr.cons (inl (silentE_fair fm)) (sttr2raw (ktr tt, tr)).
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_fair; eauto.
  Qed.

  Lemma sttr2raw_red_ub
        R tr ktr
        (NSPIN: tr <> Tr.spin)
    :
    sttr2raw (R:=R) (Vis Undefined ktr, tr) = RawTr.nb.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_ub; eauto.
  Qed.

  Lemma sttr2raw_red_ub_spin
        R tr ktr
        (SPIN: tr = Tr.spin)
    :
    sttr2raw (R:=R) (Vis Undefined ktr, tr) = raw_spin_trace.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_ub_spin; eauto.
    match goal with | |- _ = ?rhs => replace rhs with (RawTr.ob rhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    reflexivity.
  Qed.

  Lemma sttr2raw_red_nb
        R itr
    :
    sttr2raw (R:=R) (itr, Tr.nb) = RawTr.nb.
  Proof.
    match goal with | |- ?lhs = _ => replace lhs with (RawTr.ob lhs) end.
    2:{ symmetry. apply RawTr.ob_eq. }
    ss. rewrite observe_state_nb; eauto.
  Qed.



  Variable wf: WF.

  Lemma beh_diverge_index_wf_spin
        R im st
        (BEH: @Beh.diverge_index _ wf _ im st)
    :
    @wf_spin R st.
  Proof.
    revert_until R. pcofix CIH. i. punfold BEH. inv BEH.
    - pclearbot. pfold. econs. right. eauto.
    - pclearbot. pfold. econs. right. eauto.
    - pclearbot. pfold. econs. right. eauto.
    - pfold. econs.
  Qed.

  Theorem beh_of_state_wf_tr
          R im st tr
          (BEH: @Beh.of_state _ wf R im st tr)
    :
    wf_tr (st, tr).
  Proof.
    ginit. revert_until R. gcofix CIH. i. 
    induction BEH using (@of_state_ind2).
    { gstep. econs. }
    { gstep. econs. eapply beh_diverge_index_wf_spin; eauto. }
    { gstep. econs. }
    { gfinal. right. pfold. econs. eauto. }
    { guclo wf_tr_indC_spec. econs. eauto. }
    { guclo wf_tr_indC_spec. econs. eauto. }
    { guclo wf_tr_indC_spec. econs. eauto. }
    { gfinal. right. pfold. econs. }
  Qed.

  Lemma wf_tr_spin_wf_spin
        R itr
        (WF: wf_tr (R:=R) (itr, Tr.spin))
    :
    wf_spin itr.
  Proof.
    remember (itr, Tr.spin) as sttr. depgen Heqsttr. depgen itr.
    induction WF using wf_tr_ind2; i; clarify; ss.
    - pfold. econs. left. eapply IHWF. eauto.
    - pfold. econs. left. eapply IHWF. eauto.
    - pfold. econs. left. eapply IHWF. eauto.
    - pfold. econs.
  Qed.

  Lemma sttr2raw_raw_beh_spin
        R st
        (WFS: wf_spin st)
    :
    RawBeh.of_state (R:=R) st (sttr2raw (st, Tr.spin)).
  Proof.
    revert_until R. pcofix CIH. i. punfold WFS. inv WFS.
    - pclearbot. rewrite sttr2raw_red_tau; eauto; ss. pfold. econs. right. eauto.
    - pclearbot. hexploit sttr2raw_red_choose; eauto; ss.
      3:{ i. des. setoid_rewrite H0; clear H0. pfold. econs. right. eapply CIH. eapply wf_tr_spin_wf_spin; eauto. }
      2: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. rewrite sttr2raw_red_fair; eauto; ss. pfold. econs. right. eauto.
    - pfold. econs.
  Qed.

  Theorem sttr2raw_raw_beh
          R st tr
          (WF: wf_tr (st, tr))
    :
    RawBeh.of_state (R:=R) st (sttr2raw (st, tr)).
  Proof.
    revert_until R. pcofix CIH. i. remember (st, tr) as sttr. depgen st. depgen tr.
    induction WF using (@wf_tr_ind2); i; clarify.
    { rewrite sttr2raw_red_ret. pfold. econs. }
    { rewrite sttr2raw_red_obs; eauto. pfold. econs; eauto. }
    { hexploit sttr2raw_raw_beh_spin; eauto. i. eapply paco3_mon; eauto. ss. }
    { pose (classic (tr0 = Tr.nb)) as NB. des; clarify.
      { rewrite sttr2raw_red_nb. pfold. econs. }
      rewrite sttr2raw_red_tau; eauto. pfold. econs; eauto. }
    { pose (classic (tr0 = Tr.nb)) as NB. des; clarify.
      { rewrite sttr2raw_red_nb. pfold. econs. }
      hexploit sttr2raw_red_choose; eauto.
      2:{ i; des. setoid_rewrite H0; clear H0. pfold. econs; eauto. }
      pfold. econs. punfold WF. }
    { pose (classic (tr0 = Tr.nb)) as NB. des; clarify.
      { rewrite sttr2raw_red_nb. pfold. econs. }
      rewrite sttr2raw_red_fair; eauto. pfold. econs; eauto. }
    { pfold. econs. }
    { pfold. rewrite sttr2raw_red_nb. econs. }
  Qed.



  Lemma raw_spin_trace_ob
        R
    :
    raw_spin_trace = (@RawTr.ob _ R raw_spin_trace).
  Proof.
    apply RawTr.ob_eq.
  Qed.

  Lemma raw_spin_trace_spec
        R
    :
    @raw_spin _ R raw_spin_trace.
  Proof.
    pcofix CIH. rewrite raw_spin_trace_ob. pfold. econs. right. eapply CIH.
  Qed.

  Lemma sttr2raw_raw_spin
        R itr
        (WFS: @wf_spin R itr)
    :
    raw_spin (sttr2raw (itr, Tr.spin)).
  Proof.
    revert_until R. pcofix CIH; i. punfold WFS. inv WFS.
    - pclearbot. rewrite sttr2raw_red_tau; ss; eauto. pfold. econs. eauto.
    - pclearbot. hexploit sttr2raw_red_choose.
      3:{ i. des. setoid_rewrite H0; clear H0. pfold. econs. right. eapply CIH. eapply wf_tr_spin_wf_spin; eauto. }
      2: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. rewrite sttr2raw_red_fair; ss; eauto. pfold. econs. eauto.
    - rewrite sttr2raw_red_ub_spin; ss; eauto. pose raw_spin_trace_spec.
      eapply paco2_mon. eapply r0. ss.
  Qed.

  Lemma sttr2raw_extract_spin
        R st
        (WFS: @wf_spin R st)
    :
    extract_tr (sttr2raw (st, Tr.spin)) Tr.spin.
  Proof.
    ginit. revert_until R. gcofix CIH. i.
    punfold WFS. inv WFS.
    - pclearbot. rewrite sttr2raw_red_tau; ss; eauto. gfinal. right. pfold. econs.
      pfold. econs. left. eapply sttr2raw_raw_spin; eauto.
    - pclearbot. hexploit sttr2raw_red_choose.
      3:{ i. des. setoid_rewrite H0; clear H0. gfinal. right. pfold. econs.
          pfold. econs. left. eapply wf_tr_spin_wf_spin in H. eapply sttr2raw_raw_spin; eauto. }
      2: ss. pfold. econs. pfold. econs. eauto.
    - pclearbot. rewrite sttr2raw_red_fair; ss; eauto. gfinal. right. pfold. econs.
      pfold. econs. left. eapply sttr2raw_raw_spin; eauto.
    - rewrite sttr2raw_red_ub_spin; ss. gfinal. right. pfold. econs. eapply raw_spin_trace_spec.
  Qed.

  Theorem sttr2raw_extract
          R (sttr: @st_tr_im R)
          (WF: wf_tr sttr)
    :
    extract_tr (sttr2raw sttr) (snd sttr).
  Proof.
    ginit. revert_until R. gcofix CIH. i.
    pose proof WF as WF0. revert WF0.
    induction WF using wf_tr_ind2; i; clarify.
    { rewrite sttr2raw_red_ret. gfinal. right. pfold. econs. }
    { rewrite sttr2raw_red_obs; eauto. gfinal; right. pfold. econs; eauto. eapply CIH in WF. ss. right; eauto. }
    { gfinal; right. eapply sttr2raw_extract_spin in H. ss. eapply paco3_mon; eauto. ss. }
    { pose (classic (tr = Tr.nb)) as NB. des; clarify.
      { rewrite sttr2raw_red_nb. gfinal; right. pfold. econs. }
      rewrite sttr2raw_red_tau; eauto. guclo extract_tr_indC_spec. econs. eauto.
    }
    { pose (classic (tr = Tr.nb)) as NB. des; clarify.
      { rewrite sttr2raw_red_nb. gfinal; right. pfold. econs. }
      hexploit sttr2raw_red_choose.
      3:{ i; des. setoid_rewrite H0; clear H0. ss. guclo extract_tr_indC_spec. econs.
          (*TODO*)
          gfinal. right. 


          gfinal. right. pfold. econs.


          guclo extract_tr_indC_spec. econs.

          pfold. econs; eauto. right. eapply CIH.

      
      { pfold. econs. left. eapply WF0. }
      admit.
    }
    { pclearbot. pose (classic (tr = Tr.nb)) as NB. des; clarify.
      { rewrite sttr2raw_red_nb. pfold. econs. }
      rewrite sttr2raw_red_fair; eauto. pfold. econs; eauto. }
    { pfold. econs. }
    { pfold. rewrite sttr2raw_red_nb. econs. }



  Admitted.

End ExtractRaw.



Section FAIR.

  Context {Ident: ID}.
  Variable wf: WF.

  Theorem extract_preserves_fairness
          R (st: @state _ R) (im: imap wf) tr raw
          (BEH: Beh.of_state im st tr)
          (* (EXT: extract_tr raw tr) *)
    :
    RawTr.is_fair_ord wf (sttr2raw (st, tr)).
  Proof.
  Admitted.

  Theorem rawbeh_extract_is_beh
          R (st: state (R:=R)) (raw: RawTr.t (R:=R)) tr
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
          (EXT: extract_tr raw tr)
    :
    exists (im: imap wf), Beh.of_state im st tr.
  Admitted.

End FAIR.



Section EQUIV.

  Context {Ident: ID}.
  Variable wf: WF.

  Theorem IndexBeh_implies_SelectBeh
          R (st: state (R:=R)) (tr: Tr.t (R:=R)) (im: imap wf)
          (BEH: Beh.of_state im st tr)
    :
    exists raw, (<<EXTRACT: extract_tr raw tr>>) /\ (<<BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw>>).
  Proof.
  Admitted.

  Theorem SelectBeh_implies_IndexBeh
          R (st: state (R:=R)) (raw: RawTr.t (R:=R))
          (BEH: RawBeh.of_state_fair_ord (wf:=wf) st raw)
    :
    exists (im: imap wf) tr, (<<EXTRACT: extract_tr raw tr>>) /\ (<<BEH: Beh.of_state im st tr>>).
  Proof.
  Admitted.

End EQUIV.
