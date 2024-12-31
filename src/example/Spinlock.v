From sflib Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Import pind Axioms ITreeLib Red TRed IRed2 WFLibLarge.
From Fairness Require Import FairBeh Mod Linking.
From Fairness Require Import SCMem.

Module Spinlock.

  Section SPINLOCK.

    Context {state : Type}.
    Context {ident : ID}.

    Notation unlocked := (SCMem.val_nat 0).
    Notation locked := (SCMem.val_nat 1).

    Definition lock :
      ktree (threadE ident state) SCMem.val unit
      :=
      fun x =>
        ITree.iter
          (fun (_ : unit) =>
             b <- (OMod.call "cas" (x, unlocked, locked));;
             if (b : bool) then Ret (inr tt) else Ret (inl tt)) tt.

    Definition unlock :
      ktree (threadE ident state) SCMem.val unit
      :=
      fun x => (OMod.call "store" (x, unlocked)).

  End SPINLOCK.

End Spinlock.
