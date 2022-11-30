From sflib Require Import sflib.
Require Export ZArith.
(* Require Export Znumtheory. *)
Require Import List.
Require Import String.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.
Require Import Program.
From Fairness Require Import Axioms.

Set Implicit Arguments.




Require Export String.
Module Type SEAL.
  Parameter sealing: string -> forall X: Type, X -> X.
  Parameter sealing_eq: forall key X (x: X), sealing key x = x.
End SEAL.
Module Seal: SEAL.
  Definition sealing (_: string) X (x: X) := x.
  Lemma sealing_eq key X (x: X): sealing key x = x.
  Proof. reflexivity. Qed.
End Seal.

Ltac seal_with key x :=
  replace x with (Seal.sealing key x); [|eapply Seal.sealing_eq].
Ltac seal x :=
  let key := fresh "key" in
  assert (key:= "_deafult_");
  seal_with key x.
Ltac unseal x :=
  match (type of x) with
  | string => repeat rewrite (@Seal.sealing_eq x) in *; try clear x
  | _ => repeat rewrite (@Seal.sealing_eq _ _ x) in *;
         repeat match goal with
                | [ H: string |- _ ] => try clear H
                end
  end
.


Definition cast A B (LeibEq: A = B) (a: A): B := eq_rect A _ a _ LeibEq.


Module RA.
  Class t: Type := mk {
    car:> Type;
    add: car -> car -> car;
    wf: car -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    wf_mon: forall a b, wf (add a b) -> wf a;
    core: car -> option car;
    core_id: forall a c (CORE: core a = Some c), add c a = a;
    core_idem: forall a c (CORE: Some c = core a), core c = Some c;

    (* add_opt: car -> option car -> car := fun a b => match b with | Some b => add a b | _ => a end; *)
    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;

    core_mono: forall a b ca (CORE: Some ca = core a) (EXT: extends a b), exists cb, core b = Some cb /\ extends ca cb;
  }
  .

  Lemma extends_updatable
        `{M: t}
        a b
        (EXT: extends a b)
    :
      <<UPD: updatable b a>>
  .
  Proof.
    ii. rr in EXT. des. clarify. eapply wf_mon; eauto.
    rewrite <- add_assoc in H.
    rewrite <- add_assoc. rewrite (add_comm ctx). eauto.
  Qed.

  Lemma updatable_add
        `{M: t}
        a0 a1
        b0 b1
        (UPD0: updatable a0 a1)
        (UPD1: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. r in UPD0. r in UPD1.
    specialize (UPD0 (add b0 ctx)). exploit UPD0; eauto. { rewrite add_assoc. ss. } intro A.
    specialize (UPD1 (add a1 ctx)). exploit UPD1; eauto.
    { rewrite add_assoc. rewrite (add_comm b0). rewrite <- add_assoc. ss. }
    intro B.
    rewrite (add_comm a1). rewrite <- add_assoc. ss.
  Qed.

  Lemma extends_add
        `{M: t}
        a b delta
        (EXT: extends a b)
    :
      <<EXT: extends (add a delta) (add b delta)>>
  .
  Proof.
    rr in EXT. rr. des. exists ctx. subst. rewrite <- add_assoc. rewrite (add_comm a).
    symmetry. rewrite <- add_assoc. rewrite add_comm. f_equal. rewrite add_comm. ss.
  Qed.

  Program Instance extends_Transitive `{M: t}: Transitive extends.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; eauto. rewrite add_assoc. eauto.
  Qed.

  Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. eauto. Qed.

  Program Instance prod (M0 M1: t): t := {
      car := car (t:=M0) * car (t:=M1);
      add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
      wf := fun '(a0, a1) => wf a0 /\ wf a1;
      core := fun '(a0, a1) =>
                match core a0, core a1 with
                | Some a0, Some a1 => Some (a0, a1)
                | _, _ => None
                end;
    }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. split; eapply wf_mon; eauto. Qed.
  Next Obligation. des_ifs. rewrite ! core_id; auto. Qed.
  Next Obligation.
    des_ifs.
    { symmetry in Heq1, Heq2. eapply core_idem in Heq1, Heq2. clarify. }
    { symmetry in Heq2. eapply core_idem in Heq2. clarify. }
    { symmetry in Heq0. eapply core_idem in Heq0. clarify. }
  Qed.
  Next Obligation.
    des_ifs.
    { hexploit (core_mono (t:=M0)).
      { symmetry. eapply Heq1. }
      { exists c5. eauto. }
      i. des. clarify.
      hexploit (core_mono (t:=M1)).
      { symmetry. eapply Heq2. }
      { exists c6. eauto. }
      i. des. r in H0. r in H2. des. clarify. esplits; eauto.
      instantiate (1:=(_,_)). ss.
    }
    { hexploit (core_mono (t:=M1)).
      { symmetry. eapply Heq2. }
      { exists c6. eauto. }
      i. des. clarify.
    }
    { hexploit (core_mono (t:=M0)).
      { symmetry. eapply Heq0. }
      { exists c5. eauto. }
      i. des. clarify.
    }
  Qed.

  Theorem prod_updatable
          M0 M1
          (a0: @car M0) (a1: @car M1)
          (b0: @car M0) (b1: @car M1)
          (UPD0: updatable a0 b0)
          (UPD1: updatable a1 b1)
    :
      <<UPD: @updatable (prod M0 M1) (a0, a1) (b0, b1)>>
  .
  Proof.
    ii. ss. des_ifs. des. esplits; eauto.
  Qed.

  Program Instance agree (A: Type): t := {
    car := option A;
    add := fun a0 a1 => if excluded_middle_informative (a0 = a1) then a0 else None;
    wf := fun a => a <> None;
    core := fun a => Some a;
  }
  .
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.
  Next Obligation. des_ifs. Qed.
  Next Obligation.
    des_ifs.
    { esplits; eauto. des_ifs. }
    { esplits; eauto. des_ifs. eauto. }
  Qed.

  Theorem agree_unupdatable
          A
          a0 a1
    :
      <<UPD: @updatable (agree A) (Some a0) a1 -> a1 = Some a0>>
  .
  Proof.
    ii. ss. rr in H. specialize (H (Some a0)). ss. des_ifs.
    exfalso. eapply H; eauto. ss.
  Qed.

  Program Instance excl (A: Type): t := {
    car := option A;
    add := fun _ _ => None;
    wf := fun a => a <> None;
    core := fun a => None;
  }
  .

  Theorem excl_updatable
          A
          a0 a1
    :
      <<UPD: @updatable (excl A) (Some a0) a1>>
  .
  Proof. rr. ii. ss. Qed.

  Let sum_add {M0 M1} := (fun (a b: car (t:=M0) + car (t:=M1) + unit) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, _ => inr tt
                            end).
  Let sum_wf {M0 M1} := (fun (a: car (t:=M0) + car (t:=M1) + unit) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | _ => False
                           end).
  Let sum_core {M0 M1} := (fun (a: car (t:=M0) + car (t:=M1) + unit) =>
                           match a with
                           | inl (inl a0) =>
                               match core a0 with
                               | Some c => Some (inl (inl c))
                               | _ => None
                               end
                           | inl (inr a0) =>
                               match core a0 with
                               | Some c => Some (inl (inr c))
                               | _ => None
                               end
                           | inr tt => Some (inr tt)
                           end).
  Program Instance sum (M0 M1: t): t := {
    car := car (t:=M0) + car (t:=M1) + unit (* boom *);
    add := sum_add;
    wf := sum_wf;
    core := sum_core;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; eauto. Qed.
  Next Obligation.
    unfold sum_core in *. des_ifs; ss.
    { repeat f_equal. eapply core_id; auto. }
    { repeat f_equal. eapply core_id; auto. }
  Qed.
  Next Obligation.
    unfold sum_core in *. des_ifs; ss.
    { symmetry in Heq0. eapply core_idem in Heq0; auto. clarify. }
    { symmetry in Heq0. eapply core_idem in Heq0; auto. clarify. }
    { symmetry in Heq0. eapply core_idem in Heq0; auto. clarify. }
    { symmetry in Heq0. eapply core_idem in Heq0; auto. clarify. }
  Qed.
  Next Obligation.
    unfold sum_core in CORE. des_ifs; ss; des_ifs.
    { hexploit (core_mono (t:=M0)).
      { symmetry. eapply Heq. }
      { exists c1. eauto. }
      i. des. rr in H0. des. subst.
      esplits; eauto. ss. rewrite H. instantiate (1:=inl (inl _)). ss.
    }
    { ss. esplits; eauto. instantiate (1:=inr tt). ss. }
    { ss. esplits; eauto. instantiate (1:=inr tt). ss. }
    { ss. esplits; eauto. instantiate (1:=inr tt). ss. }
    { hexploit (core_mono (t:=M1)).
      { symmetry. eapply Heq. }
      { exists c1. eauto. }
      i. des. rr in H0. des. subst.
      esplits; eauto. ss. rewrite H. instantiate (1:=inl (inr _)). ss.
    }
    { ss. esplits; eauto. instantiate (1:=inr tt). ss. }
    { esplits; eauto. }
  Qed.

  Program Instance pointwise K (M: t): t := {
      car := K -> car;
      add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
      wf := fun f => forall k, wf (f k);
      core := fun _ => None;
    }
  .
  Next Obligation. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. eapply wf_mon; ss. Qed.

  Local Program Instance empty: t := {
    car := False;
    add := fun a _ => a;
    wf := fun _ => False;
    core := fun _ => None;
  }
  .
  Next Obligation. ss. Qed.

  Inductive auth_car `{M: t}: Type :=
  | auth_frag (f: option car)
  | auth_excl (e: car) (f: option car)
  | auth_boom
  .

  Let option_add `{M: t} := fun a0 a1 => match a0, a1 with
                                         | None, a1 => a1
                                         | a0, None => a0
                                         | Some a0, Some a1 => Some (add a0 a1)
                                         end.

  Let option_add_comm `{M: t} a b
    :
    option_add a b = option_add b a.
  Proof.
    destruct a, b; ss. rewrite add_comm. auto.
  Qed.

  Let option_add_assoc `{M: t} a b c
    :
    option_add a (option_add b c) = option_add (option_add a b) c.
  Proof.
    destruct a, b, c; ss. rewrite add_assoc. auto.
  Qed.

  Let option_wf `{M: t} := fun a => match a with
                                    | Some a => wf a
                                    | None => True
                                    end.

  Let auth_add `{M: t} := fun a0 a1 => match a0, a1 with
                                       | auth_frag f0, auth_frag f1 => auth_frag (option_add f0 f1)
                                       | auth_frag f0, auth_excl e1 f1 => auth_excl e1 (option_add f0 f1)
                                       | auth_excl e0 f0, auth_frag f1 => auth_excl e0 (option_add f0 f1)
                                       | _, _ => auth_boom
                                       end.

  Let auth_wf `{M: t} := fun a =>
                           match a with
                           | auth_frag f => option_wf f
                           | auth_excl e f => (match f with
                                               | Some f => extends f e
                                               | None => True
                                               end) /\ wf e
                           | auth_boom => False
                           end.

  Let option_core `{M: t} := fun a =>
                               match a with
                               | Some a => core a
                               | None => None
                               end.

  Let auth_core `{M: t} := fun a =>
                             match a with
                             | auth_frag f
                             | auth_excl _ f => Some (auth_frag (option_core f))
                             | auth_boom => Some auth_boom
                             end.

  Let option_core_mono `{M: t}
      a b
    :
    exists ctx, option_core (option_add a b) = option_add ctx (option_core a).
  Proof.
    destruct a, b; ss.
    { destruct (core c) eqn:EQ; clarify.
      { hexploit core_mono.
        { eauto. }
        { eexists. eauto. }
        i. des. rr in H0. des. subst. esplits; eauto.
        instantiate (1:=Some ctx). rewrite H. rewrite add_comm. auto.
      }
      { eexists. rewrite option_add_comm. ss. }
    }
    { exists None. ss. }
    { eexists. rewrite option_add_comm. ss. }
    { exists None. ss. }
  Qed.

  Program Instance auth (M: t): t := {
      car := auth_car;
      add := auth_add;
      wf := auth_wf;
      core := auth_core;
    }
  .
  Next Obligation.
    unfold auth_add. des_ifs.
    { rewrite option_add_comm. auto. }
    { rewrite option_add_comm. auto. }
    { rewrite option_add_comm. auto. }
  Qed.
  Next Obligation.
    unfold auth_add. des_ifs.
    { rewrite option_add_assoc. auto. }
    { rewrite option_add_assoc. auto. }
    { rewrite option_add_assoc. auto. }
    { rewrite option_add_assoc. auto. }
  Qed.
  Next Obligation.
    unfold auth_add, auth_wf, option_add, option_wf in *. des_ifs; des.
    { eapply wf_mon; eauto. }
    { rr in H. des. subst. eapply wf_mon in H0. eapply wf_mon in H0. auto. }
    { rr in H. des. subst. eapply wf_mon in H0. auto. }
    { splits; auto. etransitivity; eauto. exists c1. eauto. }
    { splits; auto. }
  Qed.
  Next Obligation.
    unfold auth_add, auth_core, option_add in *. des_ifs.
    { rewrite core_id; auto. }
    { rewrite core_id; auto. }
  Qed.
  Next Obligation.
    unfold auth_core, option_core in *. des_ifs.
    { erewrite core_idem; eauto. }
    { erewrite core_idem; eauto. }
  Qed.
  Next Obligation.
    destruct a.
    { destruct EXT.
      { ss. clarify.
        hexploit option_core_mono. i. des.
        rewrite H. esplits; eauto. instantiate (1:=auth_frag _). ss.
        rewrite option_add_comm. eauto.
      }
      { ss. clarify.
        hexploit option_core_mono. i. des.
        rewrite H. esplits; eauto. instantiate (1:=auth_frag _). ss.
        rewrite option_add_comm. eauto.
      }
      { exists auth_boom. splits; ss. exists auth_boom. destruct ca; ss. }
    }
    { destruct EXT.
      { ss. clarify.
        hexploit option_core_mono. i. des.
        rewrite H. esplits; eauto. instantiate (1:=auth_frag _). ss.
        rewrite option_add_comm. eauto.
      }
      { exists auth_boom. splits; ss. exists auth_boom. destruct ca; ss. }
      { exists auth_boom. splits; ss. exists auth_boom. destruct ca; ss. }
    }
    { ss. clarify. exists auth_boom. splits; ss. }
  Qed.

  Definition black `{M: t} (a: car): @car (auth M) := auth_excl a None.
  Definition white `{M: t} (a: car): @car (auth M) := auth_frag (Some a).

  Definition local_update `{M: t} a0 b0 a1 b1: Prop :=
    forall ctx, (<<WF: wf a0>> /\ <<FRAME: a0 = add b0 ctx>>) ->
                (<<WF: wf a1>> /\ <<FRAME: a1 = add b1 ctx>>)
  .

  Definition local_update_alloc `{M: t} a0 a1 b1: Prop :=
    (<<WF: wf a0>>) ->
    (<<WF: wf a1>> /\ <<FRAME: a1 = add b1 a0>>)
  .

  Definition local_update_dealloc `{M: t} a0 b0 a1: Prop :=
    forall ctx, (<<WF: wf a0>> /\ <<FRAME: a0 = add b0 ctx>>) ->
                (<<WF: wf a1>> /\ <<FRAME: a1 = ctx>>)
  .

  Theorem auth_wf_init
          `{M: t}
          a b
          (EXT: extends b a)
          (WF: wf a)
    :
    wf (add (black a) (white b)).
  Proof.
    ss.
  Qed.

  Theorem auth_update
          `{M: t}
          a b a' b'
          (UPD: local_update a b a' b')
    :
    <<UPD: updatable (add (black a) (white b)) (add (black a') (white b'))>>
  .
  Proof.
    rr. i. ss. rr in H. des_ifs.
    { des. rr in H. des. subst. exploit UPD.
      { esplits; eauto. rewrite add_assoc. eauto. }
      i. des. subst. splits; auto. exists ctx. rewrite add_assoc. auto.
    }
    { des. rr in H. des. subst. exploit UPD.
      { esplits; eauto. }
      i. des. subst. splits; auto. exists ctx. auto.
    }
  Qed.

  Theorem auth_dup_black
          `{M: t}
          a ca
          (CORE: a = add a ca)
    :
    <<DUP: updatable (black a) (add (black a) (white ca))>>
  .
  Proof.
    rr. ii. ss. rr in H. des_ifs.
    { des. rr in H. des. subst. esplits; eauto. exists ctx.
      rewrite CORE. rewrite <- add_assoc. rewrite add_comm. auto.
    }
    { des. splits; auto. exists e. rewrite add_comm. auto. }
  Qed.

  Theorem auth_dup_white
          `{M: t}
          a ca
          (CORE: a = add a ca)
    :
    <<DUP: updatable (white a) (add (white a) (white ca))>>
  .
  Proof.
    rr. ii. ss. rr in H. des_ifs; ss.
    { rewrite <- CORE. auto. }
    { rewrite <- CORE. auto. }
    { rewrite <- CORE. auto. }
    { rewrite <- CORE. auto. }
  Qed.

  Theorem auth_alloc
          `{M: t}
          a0 a1 b1
          (UPD: local_update_alloc a0 a1 b1)
    :
    <<UPD: updatable (black a0) (add (black a1) (white b1))>>
  .
  Proof.
    rr. i. ss. rr in H. des_ifs.
    { des. rr in H. des. subst. exploit UPD; auto.
      i. des. subst. splits; auto. exists ctx. rewrite add_assoc. auto.
    }
    { des. exploit UPD; auto.
      i. des. subst. splits; auto. exists a0. auto.
    }
  Qed.

  Theorem auth_alloc2
          `{M: t}
          a0 delta
          (WF: wf a0 -> wf (add a0 delta))
    :
    <<UPD: updatable (black a0) (add (black (add a0 delta)) (white delta))>>
  .
  Proof.
    eapply auth_alloc; eauto. ii. splits; auto. rewrite add_comm. auto.
  Qed.

  Theorem auth_dealloc
          `{M: t}
          a0 a1 b0
          (UPD: local_update_dealloc a0 b0 a1)
    :
    <<UPD: updatable (add (black a0) (white b0)) (black a1)>>
  .
  Proof.
    rr. i. ss. rr in H. des_ifs.
    { des. rr in H. des. subst. exploit UPD.
      { esplits; eauto. rewrite add_assoc. eauto. }
      i. des. subst. splits; auto. exists ctx. auto.
    }
    { des. rr in H. des. subst. exploit UPD.
      { esplits; eauto. }
      i. des. subst. splits; auto.
    }
  Qed.

  Theorem auth_included
          `{M: t}
          a b
          (WF: wf (add (black a) (white b)))
    :
    <<EXT: extends b a>>
  .
  Proof.
    rr in WF. ss. des. auto.
  Qed.

  Theorem auth_exclusive
          `{M: t}
          a b
          (WF: wf (add (black a) (black b)))
    :
    False
  .
  Proof. rr in WF. auto. Qed.

  Lemma black_wf
        `{M: t}
        a
        (WF: wf (black a))
    :
    <<WF: wf a>>
  .
  Proof. rr in WF. des; auto. Qed.
End RA.







Local Obligation Tactic := i; unseal "ra"; ss; des_ifs.

(*** PCM == Unital RA ***)
(*** When URA, not RA? (1) Auth algebra (2) global RA construction ***)
Module URA.
  Class t: Type := mk {
    car:> Type;
    unit: car;
    _add: car -> car -> car;
    _wf: car -> Prop;
    _add_comm: forall a b, _add a b = _add b a;
    _add_assoc: forall a b c, _add a (_add b c) = _add (_add a b) c;
    add: car -> car -> car := Seal.sealing "ra" _add;
    wf: car -> Prop := Seal.sealing "ra" _wf;
    unit_id: forall a, add a unit = a;
    wf_unit: wf unit;
    wf_mon: forall a b, wf (add a b) -> wf a;
    core: car -> car;
    core_id: forall a, add (core a) a = a;
    core_idem: forall a, core (core a) = core a;
    core_mono: forall a b, exists c, core (add a b) = add (core a) c;

    (* extends := fun a b => exists ctx, add a ctx = b; *)
    (* updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx); *)
    extends := fun a b => exists ctx, add a ctx = b;
    updatable := fun a b => forall ctx, wf (add a ctx) -> wf (add b ctx);
    updatable_set := fun a B => forall ctx (WF: wf (add a ctx)),
                         exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>;
  }
  .

  Lemma add_comm `{M: t}: forall a b, add a b = add b a. Proof. i. unfold add. unseal "ra". rewrite _add_comm; ss. Qed.
  Lemma add_assoc `{M: t}: forall a b c, add a (add b c) = add (add a b) c. Proof. i. unfold add. unseal "ra". rewrite _add_assoc; ss. Qed.

  Lemma wf_split `{M: t}: forall a b, wf (add a b) -> <<WF: wf a /\ wf b>>.
  Proof. i. split; eapply wf_mon; eauto. rewrite add_comm; eauto. Qed.

  Lemma extends_updatable
        `{M: t}
        a b
        (EXT: extends a b)
    :
      <<UPD: updatable b a>>
  .
  Proof.
    ii. rr in EXT. des. clarify. eapply wf_mon; eauto.
    rewrite <- add_assoc in H.
    rewrite <- add_assoc. rewrite (add_comm ctx). eauto.
  Qed.

  Lemma unit_id_ `{M: t} b (EQ: b = unit): forall a, add a b = a. i. subst. apply unit_id. Qed.

  Lemma unit_idl `{M: t}: forall a, add unit a = a. i. rewrite add_comm. rewrite unit_id; ss. Qed.

  Lemma wf_core `{M: t}: forall a (WF: wf a), wf (core a).
  Proof. i. eapply wf_mon. rewrite core_id. auto. Qed.

  Lemma unit_core `{M: t}: core unit = unit.
  Proof.
    transitivity (add (core unit) unit).
    { symmetry. apply unit_id. }
    { apply core_id. }
  Qed.

  (*** TODO: remove redundancy with "updatable_horizontal" above ***)
  Lemma updatable_add
        `{M: t}
        a0 a1
        b0 b1
        (UPD0: updatable a0 a1)
        (UPD1: updatable b0 b1)
    :
      <<UPD: updatable (add a0 b0) (add a1 b1)>>
  .
  Proof.
    ii. r in UPD0. r in UPD1.
    specialize (UPD0 (add b0 ctx)). exploit UPD0; eauto. { rewrite add_assoc. ss. } intro A.
    specialize (UPD1 (add a1 ctx)). exploit UPD1; eauto.
    { rewrite add_assoc. rewrite (add_comm b0). rewrite <- add_assoc. ss. }
    intro B.
    rewrite (add_comm a1). rewrite <- add_assoc. ss.
  Qed.

  Lemma updatable_unit
        `{M: t}
        a
    :
      <<UPD: updatable a unit>>
  .
  Proof.
    ii. rewrite unit_idl. rewrite add_comm in H. eapply wf_mon; eauto.
  Qed.

  Lemma extends_add
        `{M: t}
        a b delta
        (EXT: extends a b)
    :
      <<EXT: extends (add a delta) (add b delta)>>
  .
  Proof.
    rr in EXT. rr. des. exists ctx. subst. rewrite <- add_assoc. rewrite (add_comm a).
    symmetry. rewrite <- add_assoc. rewrite add_comm. f_equal. rewrite add_comm. ss.
  Qed.

  Lemma wf_extends
        `{M: t}
        a b
        (EXT: extends a b)
        (WF: wf b)
    :
    wf a.
  Proof.
    rr in EXT. des. subst. eapply wf_split in WF. des; auto.
  Qed.

  Lemma extends_core
        `{M: t}
        a b
        (EXT: extends a b)
    :
    extends (core a) (core b).
  Proof.
    rr in EXT. des. subst. hexploit core_mono. i. des.
    eexists. eauto.
  Qed.

  Program Instance prod (M0 M1: t): t := {
    car := car (t:=M0) * car (t:=M1);
    unit := (unit, unit);
    _add := fun '(a0, a1) '(b0, b1) => ((add a0 b0), (add a1 b1));
    _wf := fun '(a0, a1) => wf a0 /\ wf a1;
    core := fun '(a0, a1) => (core a0, core a1);
  }
  .
  Next Obligation. f_equal; rewrite add_comm; ss. Qed.
  Next Obligation. f_equal; rewrite add_assoc; ss. Qed.
  Next Obligation. f_equal; rewrite unit_id; ss. Qed.
  Next Obligation. split; eapply wf_unit. Qed.
  Next Obligation. des. split; eapply wf_mon; eauto. Qed.
  Next Obligation. f_equal; rewrite core_id; eauto. Qed.
  Next Obligation. f_equal; rewrite core_idem; eauto. Qed.
  Next Obligation.
    hexploit (core_mono c3 c1). intros [c_aux0 EQ0].
    hexploit (core_mono c4 c2). intros [c_aux1 EQ1].
    exists (c_aux0, c_aux1). rewrite EQ0. rewrite EQ1. auto.
  Qed.

  Theorem prod_updatable
          M0 M1
          (a0: @car M0) (a1: @car M1)
          (b0: @car M0) (b1: @car M1)
          (UPD0: updatable a0 b0)
          (UPD1: updatable a1 b1)
    :
      <<UPD: @updatable (prod M0 M1) (a0, a1) (b0, b1)>>
  .
  Proof.
    ii. unfold wf, add in *. unseal "ra".
    ss. des_ifs. des. esplits; eauto.
  Qed.

  Lemma prod_extends (A B: t)
        (a0 a1: @car A) (b0 b1: @car B)
    :
    @extends (prod A B) (a0, b0) (a1, b1) <-> extends a0 a1 /\ URA.extends b0 b1.
  Proof.
    split.
    { i. r in H. des. unfold add in H. unseal "ra". destruct ctx. ss. clarify.  split.
      { exists c; auto. }
      { exists c0; auto. }
    }
    { i. des. r in H. r in H0. des. subst.
      exists (ctx0, ctx). unfold add. unseal "ra". ss. unfold add. unseal "ra". f_equal.
    }
  Qed.

  Lemma prod_updatable_set (A B: t)
        (a0: @car A) (PA: @car A -> Prop)
        (b0: @car B) (PB: @car B -> Prop)
        (UPD0: URA.updatable_set a0 PA)
        (UPD1: URA.updatable_set b0 PB)
    :
    @updatable_set (prod A B) (a0, b0) (fun '(a1, b1) => PA a1 /\ PB b1).
  Proof.
    ii. destruct ctx.
    unfold wf, add in WF. unseal "ra". ss. des.
    exploit UPD0; eauto. i. des.
    exploit UPD1; eauto. i. des.
    exists (b, b1). ss. splits; ss.
    unfold wf. unseal "ra". ss. des_ifs.
    unfold add in Heq. unseal "ra". ss. clarify.
  Qed.

  Global Program Instance extends_PreOrder `{M: t}: PreOrder extends.
  Next Obligation. rr. eexists unit. ss. rewrite unit_id. ss. Qed.
  Next Obligation.
    rr. ii. rr in H. rr in H0. des. rewrite <- H0. rewrite <- H. esplits; eauto. rewrite add_assoc. eauto.
  Qed.

  Program Instance updatable_PreOrder `{M: t}: PreOrder updatable.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. r in H. r in H0. eauto. Qed.

  Lemma unfold_add `{M: t}: add = _add. Proof. unfold add. unseal "ra". reflexivity. Qed.
  (* Hint Resolve unfold_add. *)
  Lemma unfold_wf `{M: t}: wf = _wf. Proof. unfold wf. unseal "ra". reflexivity. Qed.
  (* Hint Resolve unfold_wf. *)
  Lemma unfold_wf2 `{M: t}: forall x, wf x <-> _wf x. Proof. unfold wf. unseal "ra". reflexivity. Qed.
  (* Hint Resolve unfold_wf2. *)
  Opaque add wf.









  Program Instance pointwise K (M: t): t := {
    car := K -> car;
    unit := fun _ => unit;
    _add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    _wf := fun f => forall k, wf (f k);
    core := fun f => (fun k => core (f k));
  }
  .
  Next Obligation. apply func_ext. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite unit_id. ss. Qed.
  Next Obligation. i. eapply wf_unit; ss. Qed.
  Next Obligation. i. eapply wf_mon; ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite core_id. ss. Qed.
  Next Obligation. apply func_ext. ii. rewrite core_idem. ss. Qed.
  Next Obligation.
    hexploit (choice (fun k c => core (add (a k) (b k)) = add (core (a k)) c)).
    { i. eapply core_mono. }
    intros [f EQ]. exists f. apply func_ext. i. apply EQ.
  Qed.

  Program Instance pointwise_dep K (M: K -> t): t := {
    car := forall (k: K), car (t:=M k);
    unit := fun _ => unit;
    _add := fun f0 f1 => (fun k => add (f0 k) (f1 k));
    _wf := fun f => forall k, wf (f k);
    core := fun f => (fun k => core (f k));
  }
  .
  Next Obligation. apply func_ext_dep. ii. rewrite add_comm. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite add_assoc. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite unit_id. ss. Qed.
  Next Obligation. i. eapply wf_unit; ss. Qed.
  Next Obligation. i. eapply wf_mon; ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite core_id. ss. Qed.
  Next Obligation. apply func_ext_dep. ii. rewrite core_idem. ss. Qed.
  Next Obligation.
    hexploit (non_dep_dep_functional_choice
                choice _
                (fun k c => core (add (a k) (b k)) = add (core (a k)) c)).
    { i. eapply core_mono. }
    intros [f EQ]. exists f. apply func_ext_dep. i. apply EQ.
  Qed.

  Let sum_add {M0 M1} := (fun (a b: car (t:=M0) + car (t:=M1) + bool) =>
                            match a, b with
                            | inl (inl a0), inl (inl b0) => inl (inl (add a0 b0))
                            | inl (inr a1), inl (inr b1) => inl (inr (add a1 b1))
                            | _, inr false => a
                            | inr false, _ => b
                            | _, _ => inr true
                            end).
  Let sum_wf {M0 M1} := (fun (a: car (t:=M0) + car (t:=M1) + bool) =>
                           match a with
                           | inl (inl a0) => wf a0
                           | inl (inr a1) => wf a1
                           | inr false => True
                           | inr true => False
                           end).
  Let sum_core {M0 M1} := (fun (a: car (t:=M0) + car (t:=M1) + bool) =>
                             match a with
                             | inl (inl a0) => inl (inl (core a0))
                             | inl (inr a1) => inl (inr (core a1))
                             | inr false => inr false
                             | inr true => inr true
                             end).

  Program Instance sum (M0 M1: t): t := {
    car := car (t:=M0) + car (t:=M1) + bool;
    unit := inr false;
    _add := sum_add;
    _wf := sum_wf;
    core := sum_core;
  }
  .
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_comm. Qed.
  Next Obligation. unfold sum_add. esplits; ii; ss; des; des_ifs; do 2 f_equal; apply add_assoc. Qed.
  Next Obligation. unfold sum_add. des_ifs. Qed.
  Next Obligation. unfold sum_wf in *. des_ifs; ss; des_ifs; eapply wf_mon; eauto. Qed.
  Next Obligation. unfold sum_add, sum_core. des_ifs; ss; do 2 f_equal; eapply core_id. Qed.
  Next Obligation. unfold sum_core. des_ifs; ss; do 2 f_equal; eapply core_idem. Qed.
  Next Obligation.
    pose (c := match a, b with
               | inr false, _ => sum_core b
               | _, inr false => inr false
               | inr true, _ => inr true
               | _, inr true => inr true
               | inl (inl _), inl (inr _) => inr true
               | inl (inr _), inl (inl _) => inr true
               | _, _ => inr false
               end: @car M0 + @car M1 + bool).
    destruct a as [[]|[]] eqn:EQA, b as [[]|[]] eqn:EQB; ss;
      try by (exists c; ss).
    { hexploit (@core_mono M0). i. des.
      eexists (inl (inl _)). do 2 f_equal. eauto.
    }
    { hexploit (@core_mono M1). i. des.
      eexists (inl (inr _)). do 2 f_equal. eauto.
    }
  Qed.

  Definition agree_add (A: Type) (a0 a1: option (option A)): option (option A) :=
    match a0, a1 with
    | None, _ => a1
    | _, None => a0
    | _, _ => if excluded_middle_informative (a0 = a1) then a0 else (Some None)
    end.

  Program Instance agree (A: Type): t := {
    car := option (option A);
    unit := None;
    _add := @agree_add A;
    _wf := fun a => a <> Some None;
    core := fun a => a;
  }
  .
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. unfold agree_add in *. des_ifs. Qed.
  Next Obligation. unfold agree_add. des_ifs. Qed.
  Next Obligation. exists b. auto. Qed.




  Variant gra: Type :=
    | gra_cons
        (M: RA.t)
        (a: RA.car)
    | gra_boom
  .

  Definition gra_add (a0 a1: option gra): option gra :=
    match a0, a1 with
    | None, a1 => a1
    | a0, None => a0
    | Some (@gra_cons M0 a0), Some (@gra_cons M1 a1) =>
        match (excluded_middle_informative (M0 = M1)) with
        | left e =>
            Some (@gra_cons M1 (RA.add (eq_rect _ (@RA.car) a0 _ e) a1))
        | right _ => Some gra_boom
        end
    | _, _ => Some gra_boom
    end.

  Definition gra_wf (g: gra): Prop :=
    match g with
    | @gra_cons M a => RA.wf a
    | _ => False
    end.

  Definition gen_car: Type := nat -> option gra.

  Definition gen_wf (f: gen_car): Prop :=
    (<<POINTWISE: forall k g (EQ: f k = Some g), gra_wf g>>) /\ (<<FIN: exists n, forall k (LE: n < k), f k = None>>).

  Definition gra_core (g: gra): option gra :=
    match g with
    | (@gra_cons M a) =>
        match (RA.core a) with
        | Some c => Some (@gra_cons M c)
        | None => None
        end
    | _ => Some gra_boom
    end.

  Definition gen_core (f: gen_car): gen_car :=
    fun k =>
      match (f k) with
      | None => None
      | Some g => gra_core g
      end.

  Global Program Instance gen: URA.t := {
      car := nat -> option gra;
      unit := fun _ => None;
      _add := fun f0 f1 k => gra_add (f0 k) (f1 k);
      _wf := gen_wf;
      core := gen_core;
    }
  .
  Next Obligation.
    unfold gra_add. apply func_ext.
    ii. des_ifs. dependent destruction e. ss.
    rewrite RA.add_comm. ss.
  Qed.
  Next Obligation.
    unfold gra_add. apply func_ext.
    ii. des_ifs.
    { dependent destruction H0. dependent destruction H1. dependent destruction e. ss.
      rewrite RA.add_assoc. ss.
    }
    { dependent destruction H0. dependent destruction H1. ss. }
    { dependent destruction H0. ss. }
    { dependent destruction H0. ss. }
  Qed.
  Next Obligation.
    unfold gra_add. apply func_ext.
    ii. des_ifs.
  Qed.
  Next Obligation.
    unfold gen_wf. splits; auto.
    { i. ss. }
    { exists 0. auto. }
  Qed.
  Next Obligation.
    unfold gen_wf, gra_add in *.
    des. splits; auto.
    { i. hexploit POINTWISE.
      { rewrite EQ.
        instantiate (1:= match gra_add (Some g) (b k) with
                         | Some x => x
                         | None => g
                         end).
        unfold gra_add. des_ifs; ss.
      }
      { unfold gra_add, gra_wf. des_ifs.
        { dependent destruction H0. i. eapply RA.wf_mon; eauto. }
        { dependent destruction H0. auto. }
      }
    }
    { exists n. i. hexploit FIN; eauto. i. des_ifs. }
  Qed.
  Next Obligation.
    unfold gra_add, gen_core, gra_core. apply func_ext.
    ii. des_ifs. dependent destruction H0. ss.
    rewrite RA.core_id; ss.
  Qed.
  Next Obligation.
    unfold gen_core, gra_core. apply func_ext.
    ii. des_ifs.
    { dependent destruction H0. f_equal.
      erewrite RA.core_idem in Heq0; eauto. clarify.
    }
    { dependent destruction H0.
      erewrite RA.core_idem in Heq0; eauto. clarify.
    }
  Qed.
  Next Obligation.
    unfold gen_core.
    hexploit (choice (fun (k: nat) (c: option gra) =>
                        match gra_add (a k) (b k) with
                        | Some g => gra_core g
                        | None => None
                        end
                        =
                          gra_add match a k with
                                  | Some g => gra_core g
                                  | None => None
                                  end c)).
    { i. destruct (a x) eqn:EQA.
      2:{ ss. eauto. }
      destruct g.
      2:{ exists (Some gra_boom). ss. des_ifs. }
      destruct (b x) eqn:EQB.
      2:{ exists None. ss. des_ifs. }
      destruct g.
      2:{ exists (Some gra_boom). ss. des_ifs. }
      ss. des_ifs; ss; eauto.
      { hexploit RA.core_mono; eauto.
        { eexists _. eauto. }
        i. des. rr in H0. des. ss. subst.
        rewrite H. eexists (Some (@gra_cons M0 _)). des_ifs.
        dependent destruction e. ss.
      }
      { exists (Some gra_boom). ss. }
    }
    i. des. exists f. apply func_ext.
    i. rewrite H. unfold gra_add, gra_core. des_ifs.
  Qed.

  Definition singleton `{M: RA.t} (k: nat) (m: RA.car): @URA.car gen :=
    fun n => if Nat.eq_dec n k then Some (@gra_cons M m) else None.

  Lemma singleton_wf `{M: RA.t} k m
    :
    wf (singleton k m) <-> RA.wf m.
  Proof.
    split; i.
    { rewrite URA.unfold_wf in H. rr in H.
      des. hexploit POINTWISE.
      { unfold singleton. des_ifs. }
      i. ss.
    }
    { rewrite URA.unfold_wf. rr. splits.
      { i. unfold singleton in *. des_ifs. }
      { exists k. i. unfold singleton. des_ifs. lia. }
    }
  Qed.

  Lemma singleton_add `{M: RA.t} k m0 m1
    :
    URA.add (singleton k m0) (singleton k m1)
    =
      singleton k (RA.add m0 m1).
  Proof.
    rewrite URA.unfold_add. ss.
    unfold singleton, gra_add. apply func_ext. i. des_ifs.
    dependent destruction H0. dependent destruction H1. ss.
  Qed.

  Lemma singleton_core `{M: RA.t} k m c
        (CORE: RA.core m = Some c)
    :
    URA.core (singleton k m) = singleton k c.
  Proof.
    ss. apply func_ext. i. unfold gen_core, singleton. des_ifs.
    ss. rewrite CORE. auto.
  Qed.

  Lemma singleton_updatable `{M: RA.t} k m0 m1
        (UPD: @RA.updatable M m0 m1)
    :
    URA.updatable (singleton k m0) (singleton k m1).
  Proof.
    ii. rewrite URA.unfold_wf in H. rr in H. des.
    rewrite URA.unfold_wf. ss. rr. splits.
    { i. rewrite URA.unfold_add in EQ. ss.
      cut (match add (singleton k m0) ctx k0 with
           | Some g0 => gra_wf g0
           | None => True
           end).
      2:{ des_ifs; eauto. }
      rewrite URA.unfold_add. ss.
      unfold gra_add, singleton in EQ.
      unfold gra_add, singleton. des_ifs; i; ss.
      { dependent destruction H0. ss. eapply UPD; eauto. }
      { dependent destruction H0. ss. admit. }
    }
    { exists n. i. hexploit FIN; eauto. i.
      rewrite URA.unfold_add in H. rewrite URA.unfold_add. ss.
      unfold gra_add, singleton in *. des_ifs.
    }
  Admitted.

  Lemma singleton_extends `{M: RA.t} k m0 m1
        (UPD: @RA.extends M m0 m1)
    :
    URA.extends (singleton k m0) (singleton k m1).
  Proof.
    r in UPD. des. exists (singleton k ctx).
    rewrite singleton_add. subst. auto.
  Qed.

  Lemma singleton_alloc `{M: RA.t} (m: @RA.car M) (f: @URA.car gen)
        (WF: RA.wf m)
    :
    URA.updatable_set f (fun f1 => exists k, f1 = singleton k m).
  Proof.
    ii. hexploit wf_mon.
    { rewrite add_comm. eauto. }
    intros WFF. rewrite URA.unfold_wf in WF0. rr in WF0. des.
    exists (singleton (S n) m). splits.
    { eauto. }
    hexploit (FIN (S n)).
    { lia. }
    i. rewrite URA.unfold_add in H. ss. unfold gra_add in H. des_ifs.
    rewrite URA.unfold_wf. ss. rr. split.
    { ii. rewrite URA.unfold_add in EQ. ss.
      unfold gra_add, singleton in EQ. des_ifs.
      { dependent destruction H1. ss. }
      rewrite URA.unfold_wf in WFF. ss. rr in WFF. des. eauto.
    }
    { exists (S n). i. hexploit (FIN k).
      { lia. }
      i. rewrite URA.unfold_add. rewrite URA.unfold_add in H0.
      ss. unfold gra_add, singleton in *. des_ifs. lia.
    }
  Qed.

  Lemma singleton_updatable_set `{M: RA.t} k m s
        (UPD: @RA.updatable_set M m s)
    :
    URA.updatable_set (singleton k m) (fun a => exists m1, s m1 /\ a = singleton k m1).
  Proof.
  Admitted.
End URA.

(* Coercion URA.to_RA: URA.t >-> RA.t. *)
Coercion RA.car: RA.t >-> Sortclass.
Coercion URA.car: URA.t >-> Sortclass.

Tactic Notation "ur" := try rewrite ! URA.unfold_wf; try rewrite ! URA.unfold_add; cbn.
Tactic Notation "ur" "in" hyp(H)  := try rewrite ! URA.unfold_wf in H; try rewrite ! URA.unfold_add in H; cbn in H.

Notation "'ε'" := URA.unit.
Infix "⋅" := URA.add (at level 50, left associativity).
Notation "(⋅)" := URA.add (only parsing).














Module of_RA.
Section of_RA.

Inductive car {X: Type}: Type :=
| just (x: X): car
| unit: car
.

Let wf `{M: RA.t}: car -> Prop := fun a => match a with
                                           | just a => RA.wf a
                                           | _ => True
                                           end.
Let add `{M: RA.t}: car -> car -> car :=
  fun a b =>
    match a, b with
    | just a, just b => just (RA.add a b)
    | unit, _ => b
    | _, unit => a
    end.
Let core `{M: RA.t}: car -> car :=
  fun a =>
    match a with
    | just a =>
        match RA.core a with
        | Some c => just c
        | None => unit
        end
    | _ => unit
    end.

Program Instance t (RA: RA.t): URA.t := {
  car := car;
  unit := of_RA.unit;
  _wf := wf;
  _add := add;
  core := core;
}.
Next Obligation. unfold add. des_ifs. { rewrite RA.add_comm; ss. } Qed.
Next Obligation. unfold add. des_ifs. { rewrite RA.add_assoc; ss. } Qed.
Next Obligation. unfold add. des_ifs. Qed.
Next Obligation. unfold add in *. des_ifs. eapply RA.wf_mon; eauto. Qed.
Next Obligation. unfold add, core. des_ifs. rewrite RA.core_id; eauto. Qed.
Next Obligation.
  unfold add, core. des_ifs.
  { erewrite RA.core_idem in Heq0; eauto. clarify. }
  { erewrite RA.core_idem in Heq0; eauto. clarify. }
Qed.
Next Obligation.
  destruct a; ss; eauto. destruct b; ss.
  2:{ des_ifs; ss; eauto. exists unit. eauto. }
  destruct (RA.core x) eqn:CORE; ss; eauto.
  hexploit RA.core_mono; eauto.
  { eexists. eauto. }
  i. des. rr in H0. des. subst. rewrite H. esplits; eauto.
  instantiate (1:=just _). ss.
Qed.

End of_RA.
End of_RA.

(* Coercion to_RA: t >-> RA.t. *)
Coercion of_RA.t: RA.t >-> URA.t.











Module Excl.
Section EXCL.

Context {X: Type}.
Inductive car: Type :=
| just (x: X)
| unit
| boom
.

Let _add := fun x y => match x, y with | _, unit => x | unit, _ => y | _, _ => boom end.
Let _wf := fun a => a <> boom.

Program Instance t: URA.t := {
  URA.car := car;
  URA._add := _add;
  URA._wf := _wf;
  URA.unit := unit;
  URA.core := fun _ => unit;
}
.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. unfold _wf, _add in *. des_ifs. Qed.
Next Obligation. exists unit. auto. Qed.

Theorem updatable
        a0 a1
        (WF: URA.wf a1)
  :
    <<UPD: URA.updatable (just a0) a1>>
.
Proof. rr. unfold URA.wf, URA.add in *. unseal "ra". ss. ii. des_ifs; ss. unfold _wf, _add in *. des_ifs; ss. Qed.

Theorem extends
        a0 a1
        (WF: URA.wf a1)
        (EXT: URA.extends (just a0) a1)
  :
    <<EQ: a1 = just a0>>
.
Proof. rr. rr in EXT. des; subst. unfold URA.wf, URA.add in *. unseal "ra". ss. des_ifs; ss. Qed.

Theorem wf
        a0 a1
        (WF: URA.wf (URA.add (just a0) a1))
  :
    <<EQ: a1 = unit>>
.
Proof. rr. unfold URA.wf, URA.add in *. unseal "ra". ss. des_ifs; ss. Qed.

Coercion option_coercion (x: option X): car :=
  match x with
  | Some x => just x
  | None => boom
  end
.

End EXCL.
End Excl.

Arguments Excl.t: clear implicits.
Coercion Excl.option_coercion: option >-> Excl.car.


Module Auth.
Section AUTH.

(* Variable (M: URA.t). *)

Inductive car `{M: URA.t}: Type :=
| frag (f: M)
| excl (e: M) (f: M)
| boom
.

Let add `{M: URA.t} := fun a0 a1 => match a0, a1 with
                                    | frag f0, frag f1 => frag (f0 ⋅ f1)
                                    | frag f0, excl e1 f1 => excl e1 (f0 ⋅ f1)
                                    | excl e0 f0, frag f1 => excl e0 (f0 ⋅ f1)
                                    | _, _ => boom
                                    end.
Let wf `{M: URA.t} := fun a =>
                        match a with
                        | frag f => URA.wf f
                        | excl e f => URA.extends f e /\ URA.wf e
                        | boom => False
                        end.

Let core `{M: URA.t} := fun a =>
                          match a with
                          | frag f => frag (URA.core f)
                          | excl _ f => frag (URA.core f)
                          | boom => boom
                          end.

Program Instance t (M: URA.t): URA.t := {
  car := car;
  unit := frag ε;
  _add := add;
  _wf := wf;
  core := core;
}
.
Next Obligation. subst add wf. ss. des_ifs; f_equal; eauto using URA.add_comm. Qed.
Next Obligation. subst add wf. ss. des_ifs; f_equal; eauto using URA.add_assoc. Qed.
Next Obligation. subst add wf. ss. ii; des_ifs; ss; rewrite URA.unit_id; ss. Qed.
Next Obligation. subst add wf. eauto using URA.wf_unit. Qed.
Next Obligation.
  subst add wf. ss.
  des_ifs; des; eauto using URA.wf_mon.
  - rr in H. des. subst. eapply URA.wf_mon. rewrite URA.add_assoc. eauto.
  - esplits; eauto. etransitivity; eauto. rr. ss. esplits; eauto.
Qed.
Next Obligation. subst add core. ss. des_ifs; f_equal; rewrite URA.core_id; ss. Qed.
Next Obligation. subst core. ss. des_ifs; f_equal; rewrite URA.core_idem; ss. Qed.
Next Obligation.
  destruct a.
  - destruct b.
    + hexploit (URA.core_mono f f0). intros [c EQ].
      exists (frag c). ss. f_equal. auto.
    + hexploit (URA.core_mono f f0). intros [c EQ].
      exists (frag c). ss. f_equal. auto.
    + exists boom. ss.
  - destruct b.
    + hexploit (URA.core_mono f f0). intros [c EQ].
      exists (frag c). ss. f_equal. auto.
    + exists boom. ss.
    + exists boom. ss.
  - exists boom. ss.
Qed.

Definition black `{M: URA.t} (a: M): t M := excl a ε.
Definition white `{M: URA.t} (a: M): t M := frag a.

Definition local_update `{M: URA.t} a0 b0 a1 b1: Prop :=
  forall ctx, (<<WF: URA.wf a0>> /\ <<FRAME: a0 = URA.add b0 ctx>>) ->
              (<<WF: URA.wf a1>> /\ <<FRAME: a1 = URA.add b1 ctx>>)
.

Theorem auth_update
        `{M: URA.t}
        a b a' b'
        (UPD: local_update a b a' b')
  :
    <<UPD: URA.updatable ((black a) ⋅ (white b)) ((black a') ⋅ (white b'))>>
.
Proof.
  (* rr. ur. ii; des_ifs. unseal "ra". des. *)
  rr. rewrite URA.unfold_add, URA.unfold_wf in *. ii. unseal "ra". ss. des_ifs. des.
  r in UPD. r in H. des; clarify. r in H. des; clarify.
  rewrite URA.unit_idl in *. ss.
  exploit (UPD (f ⋅ ctx)); eauto.
  { esplits; eauto. rewrite URA.add_assoc. ss. }
  i; des. clarify. esplits; eauto. rr. exists ctx. rewrite URA.add_assoc. ss.
Qed.

Theorem auth_dup_black
        `{M: URA.t}
        a ca
        (CORE: a = a ⋅ ca)
  :
    <<DUP: URA.updatable (t:=t M) (black a) ((black a) ⋅ (white ca))>>
.
Proof.
  (* r. rewrite <- unit_id at 1. *)
  (* eapply auth_update. rr. ii. des. rewrite unit_idl in FRAME. subst. *)
  (* esplits; eauto. rewrite add_comm; ss. *)
  rr. rewrite URA.unfold_add, URA.unfold_wf in *. ii. ss. des_ifs. unseal "ra". ss. des.
  rr in H. des. rewrite URA.unit_idl in *. esplits; eauto.
  rewrite CORE. eexists. rewrite <- URA.add_assoc. rewrite H. rewrite URA.add_comm. eauto.
Qed.

Theorem auth_dup_white
        `{M: URA.t}
        a ca
        (CORE: a = a ⋅ ca)
  :
    <<DUP: URA.updatable (t:=t M) (white a) ((white a) ⋅ (white ca))>>
.
Proof.
  rr. rewrite URA.unfold_add, URA.unfold_wf in *. ii. unseal "ra". ss. des_ifs.
  - ss. rewrite <- CORE. ss.
  - ss. des. esplits; eauto. rewrite <- CORE. ss.
Qed.

Theorem auth_alloc
        `{M: URA.t}
        a0 a1 b1
        (UPD: local_update a0 ε a1 b1)
  :
    <<UPD: URA.updatable (t:=t M) (black a0) ((black a1) ⋅ (white b1))>>
.
Proof.
  r. rewrite <- URA.unit_id at 1. ss. eapply auth_update. ss.
Qed.

Theorem auth_alloc2
        `{M: URA.t}
        a0 delta
        (WF: URA.wf (a0 ⋅ delta))
  :
    <<UPD: URA.updatable (t:=t M) (black a0) ((black (a0 ⋅ delta)) ⋅ (white delta))>>
.
Proof.
  rr. rewrite URA.unfold_add, URA.unfold_wf in *.
  ii. unseal "ra". ss. des_ifs. subst add wf. ss. des.
  esplits; eauto.
  rewrite URA.unit_idl in *.
  rr in H. des. rr. exists ctx; eauto. ss. clarify.
  rewrite URA.add_comm. rewrite (URA.add_comm f). rewrite <- URA.add_assoc. f_equal.
  rewrite URA.add_comm. ss.
Qed.

Theorem auth_dealloc
        `{M: URA.t}
        a0 a1 b0
        (UPD: local_update a0 b0 a1 ε)
  :
    <<UPD: URA.updatable (t:=t M) ((black a0) ⋅ (white b0)) (black a1)>>
.
Proof.
  r. rewrite <- URA.unit_id. ss. eapply auth_update. ss.
Qed.

Theorem auth_included
        `{M: URA.t}
        a b
        (WF: URA.wf ((black a) ⋅ (white b)))
  :
    <<EXT: URA.extends b a>>
.
Proof.
  rewrite URA.unfold_add in WF; rewrite URA.unfold_wf in WF.
  rr in WF. des. rr in WF. rr. des. rewrite URA.unit_idl in WF. subst. esplits; eauto.
Qed.

Theorem auth_exclusive
        `{M: URA.t}
        a b
        (WF: URA.wf ((black a) ⋅ (black b)))
  :
    False
.
Proof. rewrite URA.unfold_add in WF; rewrite URA.unfold_wf in WF. ss. Qed.

Lemma black_wf
      `{M: URA.t}
      a
      (WF: URA.wf (black a))
  :
    <<WF: URA.wf a>>
.
Proof. ur in WF. des; ss. Qed.
End AUTH.
End Auth.

(**********************************************************************************)
(*** For backward compatibility, I put below definitions "outside" Auth module. ***)
(*** TODO: put it inside ***)






Lemma nth_error_nth
      A (l: list A) n a d
      (NTH: nth_error l n = Some a)
  :
    <<NTH: nth n l d = a>>
.
Proof.
  ginduction n; ii; ss; des_ifs. ss. eapply IHn; eauto.
Qed.





Module GRA.
  Class t: Type := __GRA__INTERNAL__: (nat -> URA.t).
  Class inG (RA: URA.t) (Σ: t) := InG {
    inG_id: nat;
    (* inG_prf: Eq (GRA inG_id) RA; *)
    inG_prf: RA = Σ inG_id;
  }
  .
  Class subG (Σ0 Σ1: t) := SubG i : { j | Σ0 i = Σ1 j }.
  (* Class subG (GRA0 GRA1: t) := SubG { subG_prf: forall i, { j | GRA0 i = GRA1 j } }. *)

  Definition of_list (RAs: list URA.t): t := fun n => List.nth n RAs (of_RA.t RA.empty).

  Definition to_URA (Σ: t): URA.t := URA.pointwise_dep Σ.

  Coercion to_URA: t >-> URA.t.

  Let cast_ra {A B: URA.t} (LeibEq: A = B) (a: URA.car (t:=A)): URA.car (t:=B) :=
    eq_rect A (@URA.car) a _ LeibEq.

  (* a: URA.car =ty= RAs inG_id =ty= RAs n *)
  Definition embed {A Σ} `{@GRA.inG A Σ} (a: URA.car (t:=A)): URA.car (t:=Σ) :=
    fun n => match Nat.eq_dec inG_id n with
             | left H => ((@eq_rect nat inG_id Σ ((cast_ra inG_prf a): Σ inG_id) n H): Σ n)
             | right _ => URA.unit
             end
  .

  Lemma embed_wf
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: URA.wf (embed a))
    :
      <<WF: URA.wf a>>
  .
  Proof.
    rewrite URA.unfold_wf in WF.
    r. specialize (WF inG_id). ss. unfold embed in *. des_ifs.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *. dependent destruction e. destruct inG_prf. ss.
  Qed.

  Lemma wf_embed
        A Σ
        `{@GRA.inG A Σ}
        (a: A)
        (WF: URA.wf a)
    :
      <<WF: URA.wf (embed a)>>
  .
  Proof.
    destruct H. subst. rewrite URA.unfold_wf.
    r. ii. unfold embed. des_ifs.
    eapply URA.wf_unit.
  Qed.

  Lemma embed_add
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
    :
      <<EQ: URA.add (embed a0) (embed a1) = embed (URA.add a0 a1)>>
  .
  Proof.
    rewrite URA.unfold_add in *.
    r. ss. unfold embed. apply func_ext_dep. i. des_ifs.
    - ss. unfold cast_ra. unfold eq_rect, eq_sym. destruct inG_prf. reflexivity.
    - rewrite URA.unit_id. ss.
  Qed.

  Lemma embed_updatable
        A Σ
        `{@GRA.inG A Σ}
        (a0 a1: A)
        (UPD: URA.updatable a0 a1)
    :
      <<UPD: URA.updatable (GRA.embed a0) (GRA.embed a1)>>
  .
  Proof.
    r in UPD. ii. ss.
    rewrite URA.unfold_add in *. rewrite URA.unfold_wf in *. ss. ii.
    rename H0 into WF.
    specialize (WF k).
    unfold embed in *. des_ifs. ss.
    unfold cast_ra in *. unfold eq_rect, eq_sym in *.
    destruct H. ss.
    dependent destruction inG_prf0.
    eapply UPD. ss.
  Qed.

  Section GETSET.
    Variable ra: URA.t.
    Variable gra: t.
    Context `{@inG ra gra}.

    Section GETSET.
    Variable get: URA.car (t:=ra).
    Variable set: URA.car (t:=ra) -> unit.

    (* own & update can be lifted *)
    (* can we write spec in terms of own & update, not get & set? *)
    (* how about add / sub? *)
    Program Definition get_lifted: URA.car (t:=gra) :=
      fun n => if Nat.eq_dec n inG_id then _ else URA.unit.
    Next Obligation.
      apply (cast_ra inG_prf get).
    Defined.

    (* Program Definition set_lifted: URA.car (t:=construction gra) -> unit := *)
    (*   fun n => if Nat.eq_dec n inG_id then _ else URA.unit. *)
    (* Next Obligation. *)
    (*   apply (ra_transport inG_prf get). *)
    (* Defined. *)
    End GETSET.

    Section HANDLER.
    Variable handler: URA.car (t:=ra) -> URA.car (t:=ra).
    Local Obligation Tactic := idtac.
    Program Definition handler_lifted: URA.car (t:=gra) -> URA.car (t:=gra) :=
      fun st0 => fun n => if Nat.eq_dec n inG_id then _ else st0 n
    .
    Next Obligation.
      i. subst. simpl in st0. specialize (st0 inG_id).
      rewrite <- inG_prf in st0. specialize (handler st0). rewrite <- inG_prf. apply handler.
    Defined.

    End HANDLER.

  End GETSET.

  Section CONSTRUCTION.
    Variable RAs: list URA.t.
    Let GRA: t := (fun n => List.nth n RAs RA.empty).
    Theorem construction_adequate: forall n RA (IN: List.nth_error RAs n = Some RA),
        inG RA GRA.
    Proof.
      i. unshelve econs; eauto. unfold GRA. symmetry. eapply nth_error_nth; eauto.
    Qed.

    (* Let GRA2: RA.t := URA.pointwise_dep GRA. *)
    (* Goal @RA.car GRA2 = forall k, (@RA.car (GRA k)). ss. Qed. *)
  End CONSTRUCTION.

  (* Definition extends (RA0 RA1: URA.t): Prop := *)
  (*   exists c, URA.prod RA0 c = RA1 *)
  (* . *)

  Class inG2 (RA GRA: URA.t): Prop := {
    GRA_data: t;
    (* GRA_prf:  *)
    inG2_id: nat;
    inG2_prf: GRA_data inG2_id = RA;
  }
  .

  Fixpoint point_wise_wf (Ml: list URA.t) (x: of_list Ml) (n: nat) :=
  match n with
  | O => True
  | S n' => @URA.wf (of_list Ml n') (x n') /\ @point_wise_wf Ml x n'
  end.

  Definition point_wise_wf_lift (Ml: list URA.t) (x: of_list Ml)
             (POINT: point_wise_wf x (List.length Ml))
    :
      @URA.wf (of_list Ml) x.
  Proof.
    ur. ss. i. unfold of_list in *.
    assert (WF: forall (n m: nat)
                       (POINT: point_wise_wf x n)
                       (LT: (m < n)%nat),
               URA.wf (x m)).
    { induction n.
      { i. inv LT. }
      { i. ss. des. inv LT; auto. }
    }
    destruct (le_lt_dec (List.length Ml) k).
    { generalize (x k). rewrite nth_overflow; auto. i. ur. destruct c; ss. }
    { eapply WF; eauto. }
  Qed.

  Lemma point_add (G: t) (x0 x1: G) n
    :
      (x0 ⋅ x1) n = x0 n ⋅ x1 n.
  Proof.
    ur. ss. ur. auto.
  Qed.
End GRA.
Coercion GRA.to_URA: GRA.t >-> URA.t.

Global Opaque GRA.to_URA.
(* Definition ε `{Σ: GRA.t}: Σ := URA.unit. *)

(***
Choose: non-det
Take: angelic non-det
(*** empty choose : NB ***)
(*** empty take : UB ***)
x <- Choose X ;; guarantee (P x) ;; k x   (~=) x <- Choose { X | P x } ;; k x
x <- Take X   ;; assume (P x)    ;; k x   (~=) x <- Take { X | P x }   ;; k x
guarantee P ;; assume P ;; k              (~=) guarantee P ;; k
x <- Take X ;; pure ;; k x                (>=) pure ;; x <- Take X ;; k x
pure ;; x <- Choose X ;; k x              (>=) x <- Choose X ;; pure ;; k x
______________caller______________    _________________callee_________________   _caller_
x0 <- Choose X ;; guarantee (P x0) ;; (x1 <- Take X ;; assume (P x1) ;; k1 x1) ;; k0 x0
(<=)
x0 <- Choose X ;; x1 <- Take X ;; guarantee (P x0) ;; assume (P x1) ;; k1 x1 ;; k0 x0
(<=)
x <- Choose X ;; guarantee (P x) ;; assume (P x) ;; k1 x ;; k0 x
(<=)
x <- Choose X ;; guarantee (P x) ;; k1 x ;; k0 x
Goal forall X Y (k: X -> Y),
    x <- trigger (EChoose X) ;; Ret (k x) =
    y <- trigger (EChoose {y | exists x, y = k x}) ;; Ret (proj1_sig y)
.
Abort.
***)


Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V') (at level 55, right associativity): ra_scope.
From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.


Section TEST.
  Variable A B C: Type.
  Let _myRA: URA.t := (A ==> B ==> (RA.excl C))%ra.
  Let myRA: URA.t := Auth.t _myRA.
End TEST.

Ltac r_first rs :=
  match rs with
  | (?rs0 ⋅ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

Ltac r_solve :=
  repeat rewrite URA.add_assoc;
  repeat (try rewrite URA.unit_id; try rewrite URA.unit_idl);
  match goal with
  | [|- ?lhs = (_ ⋅ _) ] =>
    let a := r_first lhs in
    try rewrite <- (URA.add_comm a);
    repeat rewrite <- URA.add_assoc;
    try (eapply f_equal; r_solve)
  | _ => try reflexivity
  end
.

Lemma prop_ext_rev
      A B
      (EQ: A = B)
  :
    A <-> B
.
Proof. clarify. Qed.

Ltac r_wf H := eapply prop_ext_rev; [eapply f_equal|]; [|eapply H]; r_solve.

Ltac g_wf_tac :=
  cbn; repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl;
  apply GRA.point_wise_wf_lift; ss; splits; repeat rewrite GRA.point_add; unfold GRA.embed; ss;
  repeat rewrite URA.unit_id; repeat rewrite URA.unit_idl; try apply URA.wf_unit.

Global Opaque URA.unit.

Section UNIT.

  Program Instance Unit : URA.t := {| URA.unit := tt; URA._add := fun _ _ => tt; URA._wf := fun _ => True; URA.core := fun _ => tt; |}.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.
  Next Obligation. unseal "ra". i. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. unseal "ra". i. exists tt. ss. Qed.

  Lemma Unit_wf : forall x, @URA.wf Unit x.
  Proof. unfold URA.wf. unseal "ra". ss. Qed.

End UNIT.

Section URA_PROD.

  Lemma unfold_prod_add (M0 M1 : URA.t) : @URA.add (URA.prod M0 M1) = fun '(a0, a1) '(b0, b1) => (a0 ⋅ b0, a1 ⋅ b1).
  Proof. rewrite URA.unfold_add. extensionalities r0 r1. destruct r0, r1. ss. Qed.

  Lemma unfold_prod_wf (M0 M1 : URA.t) : @URA.wf (URA.prod M0 M1) = fun r => URA.wf (fst r) /\ URA.wf (snd r).
  Proof. rewrite URA.unfold_wf. extensionalities r. destruct r. ss. Qed.

End URA_PROD.

Section POINTWISE.

  Lemma unfold_pointwise_add X (M: URA.t) (f0 f1: (X ==> M)%ra)
    :
    f0 ⋅ f1 = (fun x => f0 x ⋅ f1 x).
  Proof.
    ur. ur. auto.
  Qed.

  Lemma updatable_set_impl (M: URA.t)
        (P0 P1: M -> Prop)
        (IMPL: forall r, URA.wf r -> P0 r -> P1 r)
        (m: M)
        (UPD: URA.updatable_set m P0)
    :
    URA.updatable_set m P1.
  Proof.
    ii. eapply UPD in WF; eauto. des.
    esplits; eauto. eapply IMPL; auto.
    eapply URA.wf_mon. eauto.
  Qed.

  Lemma pointwise_extends A (M: URA.t)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, URA.extends (f0 a) (f1 a))
    :
    URA.extends f0 f1.
  Proof.
    hexploit (choice (fun a ctx => f1 a = (f0 a) ⋅ ctx)).
    { i. specialize (UPD x). r in UPD. des. eauto. }
    i. des. exists f.
    rewrite (@unfold_pointwise_add A M). extensionality a. auto.
  Qed.

  Lemma pointwise_updatable A (M: URA.t)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, URA.updatable (f0 a) (f1 a))
    :
    URA.updatable f0 f1.
  Proof.
    ii. ur. i. ur in H. specialize (H k).
    eapply (UPD k); eauto.
  Qed.

  Lemma pointwise_updatable_set A (M: URA.t)
        (f: (A ==> M)%ra)
        (P: A -> M -> Prop)
        (UPD: forall a, URA.updatable_set (f a) (P a))
    :
    URA.updatable_set f (fun f' => forall a, P a (f' a)).
  Proof.
    ii. hexploit (choice (fun a m => P a m /\ URA.wf (m ⋅ ctx a))).
    { i. eapply (UPD x). ur in WF. auto. }
    i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { ur. i. specialize (H k). des. auto. }
  Qed.

  Definition maps_to_res {A} {M: URA.t}
             a m: (A ==> M)%ra :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else URA.unit.

  Lemma maps_to_res_add A (M: URA.t)
        (a: A) (m0 m1: M)
    :
    maps_to_res a m0 ⋅ maps_to_res a m1
    =
      maps_to_res a (m0 ⋅ m1).
  Proof.
    extensionality a'. unfold maps_to_res. ur. des_ifs.
    { ur. auto. }
    { r_solve. }
  Qed.

  Lemma maps_to_updatable A (M: URA.t)
        (a: A) (m0 m1: M)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (maps_to_res a m0) (maps_to_res a m1).
  Proof.
    eapply pointwise_updatable. i.
    unfold maps_to_res. des_ifs.
  Qed.

  Lemma maps_to_updatable_set A (M: URA.t)
        (a: A) (m: M) (P: M -> Prop)
        (UPD: URA.updatable_set m P)
    :
    URA.updatable_set
      (maps_to_res a m)
      (fun f => exists (m1: M), f = maps_to_res a m1 /\ P m1).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P m') /\ (a' <> a -> m' = URA.unit)).
      ii. unfold maps_to_res in WF. des_ifs.
      { exploit UPD; eauto. i. des. esplits; eauto. ss. }
      { exists URA.unit. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionality a'. unfold maps_to_res. des_ifs.
        specialize (H0 a'). des. auto.
      }
      { specialize (H0 a). des. auto. }
    }
  Qed.

  Definition map_update {A} {M: URA.t}
             (f: (A ==> M)%ra) a m :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else f a'.

End POINTWISE.


Tactic Notation "unfold_prod" :=
  try rewrite ! unfold_prod_add;
  rewrite unfold_prod_wf;
  simpl.

Tactic Notation "unfold_prod" hyp(H) :=
  try rewrite ! unfold_prod_add in H;
  rewrite unfold_prod_wf in H;
  simpl in H;
  let H1 := fresh H in
  destruct H as [H H1].

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.


Section AUX.
  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; eauto. Qed.

  Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pw_add_disj_wf
        (f g: K -> M)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. specialize (DISJ k). des; rewrite DISJ.
    - rewrite URA.unit_idl; eauto.
    - rewrite URA.unit_id; eauto.
  Qed.

  Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
      <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
  Proof.
    i. unfold insert, functions.fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
  Qed.

  Lemma lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.
End AUX.



(* TODO: make lemmas for RA and turn it into URA at the last *)

From Fairness Require LPCM.

Program Definition to_LURA (M: URA.t): LPCM.URA.t :=
  @LPCM.URA.mk M.(URA.car) M.(URA.unit) M.(URA._add) M.(URA._wf) M.(URA._add_comm) M.(URA._add_assoc) _ _ _ M.(URA.core) _ _ _.
Next Obligation.
  i. LPCM.unseal "ra".
  hexploit URA.unit_id. i. ur in H. eauto.
Qed.
Next Obligation.
  i. LPCM.unseal "ra".
  hexploit URA.wf_unit. i. ur in H. eauto.
Qed.
Next Obligation.
  i. LPCM.unseal "ra".
  hexploit URA.wf_mon.
  { ur. eauto. }
  i. ur in H0. eauto.
Qed.
Next Obligation.
  i. LPCM.unseal "ra".
  hexploit URA.core_id. i. ur in H. eauto.
Qed.
Next Obligation.
  i. LPCM.unseal "ra".
  hexploit URA.core_idem. i. ur in H. eauto.
Qed.
Next Obligation.
  i. LPCM.unseal "ra".
  hexploit URA.core_mono. i. ur in H. eauto.
Qed.

Coercion to_LURA: URA.t >-> LPCM.URA.t.
