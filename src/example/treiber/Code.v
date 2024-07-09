From sflib Require Import sflib.
From Fairness Require Import Mod Linking.
From Fairness Require Import SCMemSpec.

Module TreiberStack.

  Section TREIBERSTACK.

    Context {state : Type}.
    Context {ident : ID}.

    Definition push_loop :
      ktree (threadE ident state) (SCMem.val * SCMem.val) (unit + unit)
      := fun '(s, node) =>
        head <- (OMod.call (R:=SCMem.val) "load" s);;
        _ <- (OMod.call (R:=unit) "store" (node,head));;
        b <- (OMod.call (R:=bool) "cas" (s, head, node));;
        if b then Ret (inr tt) else Ret (inl tt).

    Definition push :
      (* ktree (threadE void unit) (SCMem.val * SCMem.val) unit *)
      ktree (threadE ident state) (SCMem.val * SCMem.val) unit
      :=
      fun '(s,val) =>
        node <- (OMod.call (R:=SCMem.val) "alloc" 2);;
        _ <- (OMod.call (R:=unit) "store" (SCMem.val_add node 1, val));;
        _ <- ITree.iter (fun (_ : unit) => push_loop (s, node)) tt;;
        trigger Yield.

    Definition pop_loop :
      ktree (threadE ident state) SCMem.val (unit + option (SCMem.val))
      :=
      fun s =>
        head <- (OMod.call (R:=SCMem.val) "load" s);;
        is_null <- (OMod.call (R:=bool) "compare" (head, SCMem.val_null));;
        if is_null then Ret (inr None) else
        next <- (OMod.call (R:=SCMem.val) "load" head);;
        b <- (OMod.call (R:=bool) "cas" (s, head, next));;
        if b then
          data <- (OMod.call (R:=SCMem.val) "load" (SCMem.val_add head 1));;
          Ret (inr (Some data))
        else
          Ret (inl tt)
        .

    Definition pop :
      (* ktree (threadE void unit) SCMem.val (option (SCMem.val) *)
      ktree (threadE ident state) SCMem.val (option (SCMem.val))
      :=
      fun s =>
        _ <- trigger Yield;;
        ITree.iter (fun (_ : unit) => pop_loop s) tt.

    (** TODO : more rules for module composition. *)
    (* Definition omod : Mod.t := *)
    (*   Mod.mk *)
    (*     (* tt *) *)
    (*     (Mod.st_init Client) *)
    (*     (Mod.get_funs [("push", Mod.wrap_fun push); *)
    (*                    ("pop", Mod.wrap_fun pop)]) *)
    (* . *)

    (* Definition module gvs : Mod.t := *)
    (*   OMod.close *)
    (*     (omod) *)
    (*     (SCMem.mod gvs) *)
    (* . *)

  End TREIBERSTACK.
End TreiberStack.
