From sflib Require Import sflib.
From Paco Require Import paco.
From Fairness Require Export FairBeh Mod Linking WMM FairLock Concurrency LockClientW FIFOSched SchedSim FIFOSched FIFOSchedSim ModAdequacy TicketLockW ModCloseSim ModAddSim.

Section ALL.
  Definition client_spec := ClientSpec.mod.

  Definition client_abstract_lock :=
    OMod.close ClientImpl.omod (ModAdd WMem.mod AbsLockW.mod).

  Definition client_ticket_lock :=
    OMod.close ClientImpl.omod (ModAdd WMem.mod TicketLockW.mod ).

  Lemma client_all_aux
    :
    Adequacy.improves
      (interp_all
         (client_spec.(Mod.st_init))
         (prog2ths client_spec [("thread1", tt↑); ("thread2", tt↑)]) 0)
      (interp_all_fifo
         (client_ticket_lock.(Mod.st_init))
         (prog2ths client_ticket_lock [("thread1", tt↑); ("thread2", tt↑)]) 0)
  .
  Proof.
    eapply Adequacy.improves_trans.
    { eapply Adequacy.adequacy.
      { instantiate (1:=nat_wf). econs. exact 0. }
      { i. ss. eauto. }
      { eapply ssim_implies_gsim; ss.
        { instantiate (1:=id). ss. }
        { eapply ssim_nondet_fifo; ss. ii. compute in H. des. inv H; des; ss. inv H1; ss. }
      }
    }
    eapply Adequacy.improves_trans.
    { eapply modsim_adequacy. eapply ModClose_mono.
      eapply ModAdd_right_mono. eapply TicketLockFair.ticketlock_fair.
    }
    { eapply usersim_adequacy. eapply LockClientWCorrect.correct. }
    Unshelve. all: econs.
  Qed.

  Theorem client_all
    :
    Adequacy.improves
      (interp_concurrency
         (prog2ths client_spec [("thread1", tt↑); ("thread2", tt↑)])
         (sched_nondet _)
         (client_spec.(Mod.st_init))
      )
      (interp_concurrency
         (prog2ths client_ticket_lock [("thread1", tt↑); ("thread2", tt↑)])
         (sched_fifo_set _)
         (client_ticket_lock.(Mod.st_init))
      )
  .
  Proof.
    eapply client_all_aux.
  Qed.

End ALL.
