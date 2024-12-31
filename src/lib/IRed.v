From Fairness Require Import Red ITreeLib Any FairBeh.
From sflib Require Import sflib.
Require Import Program.

Local Open Scope nat_scope.

Set Implicit Arguments.



Ltac get_head term :=
  match term with
  | ?f ?x => get_head f
  | _ => term
  end
.

Ltac get_head2 term :=
  lazymatch term with
  | ?f ?x =>
    let ty := type of x in
    lazymatch ty with
    | context[ReSum] => term
    | _ => get_head2 f
    end
  | _ => term
  end
.

Ltac get_itr term :=
  match term with
  | _ ?x => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ _ => match type of x with itree _ _ => constr:(x) end
  | _ ?x _ _ _ _ _ => match type of x with itree _ _ => constr:(x) end
  end
.

Ltac get_nth term n :=
  match term with
  | ?f ?x =>
    match n with
    | O => x
    | S ?m => get_nth f m
    end
  | ?x =>
    match n with
    | O => x
    end
  end
.

Goal forall (f: nat -> nat -> nat -> nat -> nat) a b c d, f a b c d = 0.
  i.
  let tmp := get_nth (f a b c d) 0 in pose tmp as d'. assert(d' = d) by reflexivity.
  let tmp := get_nth (f a b c d) 1 in pose tmp as c'. assert(c' = c) by reflexivity.
  let tmp := get_nth (f a b c d) 2 in pose tmp as b'. assert(b' = b) by reflexivity.
  let tmp := get_nth (f a b c d) 3 in pose tmp as a'. assert(a' = a) by reflexivity.
  let tmp := get_nth (f a b c d) 4 in pose tmp as f'. assert(f' = f) by reflexivity.
Abort.



Variant Box: Type :=
| mk_box: forall (A:Type), A -> Box
.

Class red_database (interp: Box) := mk_rdb {
  rdb_pos: nat;
  rdb_bind: Box;
  rdb_tau: Box;
  rdb_ret: Box;
  rdb_trigger0: Box;
  rdb_trigger1: Box;
  rdb_trigger2: Box;
  rdb_trigger3: Box;
  rdb_trigger4: Box;
  rdb_trigger5: Box;
  rdb_trigger6: Box;
  rdb_UB: Box;
  rdb_NB: Box;
  rdb_unwrapU: Box;
  rdb_unwrapN: Box;
  rdb_assume: Box;
  rdb_guarantee: Box;
  rdb_ext: Box;
}
.
Arguments mk_rdb [interp].
Arguments rdb_pos [interp].
Arguments rdb_bind [interp].
Arguments rdb_tau [interp].
Arguments rdb_ret [interp].
Arguments rdb_trigger0 [interp].
Arguments rdb_trigger1 [interp].
Arguments rdb_trigger2 [interp].
Arguments rdb_trigger3 [interp].
Arguments rdb_trigger4 [interp].
Arguments rdb_trigger5 [interp].
Arguments rdb_trigger6 [interp].
Arguments rdb_UB [interp].
Arguments rdb_NB [interp].
Arguments rdb_unwrapU [interp].
Arguments rdb_unwrapN [interp].
Arguments rdb_assume [interp].
Arguments rdb_guarantee [interp].
Arguments rdb_ext [interp].






Ltac _red_itree f :=
  lazymatch goal with
  | [ |- ITree.bind ?itr ?ktr = _] =>
    lazymatch itr with
    | ITree.bind _ _ =>
      instantiate (f:=_continue); apply bind_bind; fail
    | Tau _ =>
      instantiate (f:=_break); apply bind_tau; fail
    | Ret _ =>
      instantiate (f:=_continue); apply bind_ret_l; fail
    end
  | [ |- trigger _ = _] =>
    instantiate (f:=_break); apply bind_ret_r_rev; fail
  | _ => fail
  end.

Ltac __red_interp f term :=
  match term with
  | unwrap (@Any.downcast ?A (@Any.upcast ?A ?a)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.upcast_downcast; fail
  | unwrap (Any.split (Any.pair ?a0 ?a1)) =>
    instantiate (f:=_continue); apply f_equal; apply Any.pair_split; fail
  | _ =>

  let my_interp := get_head2 term in
  let tc := fresh "_TC_" in
  unshelve evar (tc: @red_database (mk_box (my_interp))); [typeclasses eauto|];
  let name := fresh "TMP" in
  let _nth := constr:(rdb_pos tc) in
  let nth := (eval simpl in _nth) in
  let itr := get_nth term nth in
  lazymatch itr with
  | ITree.bind ?i0 ?k0 =>
    instantiate (f:=_continue); pose (rdb_bind tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => first[apply (@lemma _ _ i0 k0)|apply lemma] end
  | Tau _ =>
    instantiate (f:=_continue); pose (rdb_tau tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | Ret _ =>
    instantiate (f:=_continue); pose (rdb_ret tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | trigger ?e =>
    instantiate (f:=_continue);
    ((pose (rdb_trigger0 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger1 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger2 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger3 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger4 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger5 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     (pose (rdb_trigger6 tc) as name; cbn in name; match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end) ||
     fail 3
    )
  | UB =>
    instantiate (f:=_continue); pose (rdb_UB tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | unwrap _ =>
    instantiate (f:=_continue); pose (rdb_unwrapU tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma; fail 2 end
  | ?term =>
    pose (rdb_ext tc) as name; cbn in name;
    match goal with | name := mk_box ?lemma |- _ => apply lemma end;
    subst tc;
    __red_interp f term
  end
end
.

Ltac _red_interp f :=
  lazymatch goal with
  | [ |- ITree.bind ?term _ = _ ] =>
    apply bind_ext; __red_interp f term
  | [ |- ?term = _] =>
    __red_interp f term
  end
.

Ltac _red_gen f :=
  _red_interp f || _red_itree f || fail.
