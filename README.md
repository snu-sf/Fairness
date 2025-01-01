# Lilo
This artifact contains Coq development for the paper *Lilo: A Higher-Order, Relational Concurrent Separation Logic for Liveness*.

## Build
Requirement: `opam` (>=2.0.0). You can run `opam --version` to check if `opam` is installed. You will need at least version 2.0.0. If `opam` is not already installed, follow instructions at: https://opam.ocaml.org/doc/Install.html
- Create and initialize a new opam switch
```
opam switch create . ocaml-base-compiler.4.14.2 --no-install
eval $(opam env)
```
- Install dependencies with opam
```
./configure
```
- Build the project
```
make -j
```

## Code Structure
### Definitions and Rules
Note that definitions and rules in the development are more general compared to the corresponding ones presented in the paper.
Also, the development includes the full detail related to the stratified propositions.

#### Section 3
- progress credits (◇<sub>𝜅</sub>(ℓ, n)) (Sec 3.1) : `progress_credit` in `src/tlogic/LiveObligations.v`
- obligation lists (Obls<sub>th</sub>(Φ)) (Sec 3.1): `duty` in `src/tlogic/LiveObligations.v`
- CRED-NEW (Sec 3.1, Fig.1) : `alloc_obligation_fine` in `src/tlogic/LiveObligations.v`
- PC-SPLIT (Sec 3.1, Fig.1) : `pc_split` in `src/tlogic/LiveObligations.v`
- PC-DROP (Sec 3.1, Fig.1) : `pc_drop` in `src/tlogic/LiveObligations.v`
- OBLS-ADD (Sec 3.1, Fig.1) : `duty_add` in `src/tlogic/LiveObligations.v`
- OBLS-FULFILL (Sec 3.1, Fig.1) : `duty_fulfill` in `src/tlogic/LiveObligations.v`
- PROM-GET (Sec 3.1, Fig.1) : `duty_tpromise` in `src/tlogic/LiveObligations.v`
- scheduler credit (€) (Sec 3.2) : `thread_credit` in `src/tlogic/LiveObligations.v`
- promise (Sec 3.2, Fig.2) : `thread_promise` in `src/tlogic/LiveObligations.v`
- credit bound (◆<sub>𝜅</sub>⌈ℓ, n⌉) (Sec 3.2, Fig.2) : `liveness_obligation_fine` in `src/tlogic/LiveObligations.v`
- PROM-PERS (Sec 3.2, Fig.2) : `Persistent_thread_promise` in `src/tlogic/LiveObligations.v`
- PROM-PROGRESS (Sec 3.2, Fig.2) : `tpromise_progress` in `src/tlogic/LiveObligations.v`
- CB-PERS (Sec 3.2, Fig.2) : `Persistent_liveness_obligation_fine` in `src/tlogic/LiveObligations.v`
- CRED-IND (Sec 3.2, Fig.2) : `lo_ind_fine` in `src/tlogic/LiveObligations.v`
- simulation weakest precondition (Sec 3.3, Fig.3) : `wpsim` in `src/tlogic/SimWeakest.v`
- INV-ALLOC (Sec 3.3, Fig.3) : `FUpd_alloc` in `src/ra/IndexedInvariants.v`
- INV-PERS (Sec 3.3, Fig.3) : `OwnI_persistent` in `src/ra/IndexedInvariants.v`
- INV-OPEN (Sec 3.3, Fig.3) : `FUpd_open` in `src/ra/IndexedInvariants.v`
- INV-CLOSE (Sec 3.3, Fig.3) : `FUpd_open` in `src/ra/IndexedInvariants.v`
- MEM-READ (Sec 3.3, Fig.3) : `SCMem_load_fun_spec` in `src/example/SCMemSpec.v`
- MEM-WRITE (Sec 3.3, Fig.3) : `SCMem_store_fun_spec` in `src/example/SCMemSpec.v`
- YIELD-TGT (Sec 3.3, Fig.3) : `wpsim_yieldR_gen` in `src/tlogic/SimWeakest.v`
- SIM-TERM (Sec 3.3, Fig.3) : `wpsim_ret` in `src/tlogic/SimWeakest.v`
- Theorem 3.1 (Adequacy) : `Theorem whole_sim_implies_refinement` in `src/tlogic/SimWeakestAdequacy.v` (the paper presents a simplified form)

#### Section 4
- obligation link (κ1 -◇ κ2) (Sec 4.2, Fig.4) : `link` in `src/tlogic/LiveObligations.v`
- LINK-PERS (Sec 4.2, Fig.4) : `Persistent_link` in `src/tlogic/LiveObligations.v`
- LINK-NEW (Sec 4.2, Fig.4) : `link_new_fine` in `src/tlogic/LiveObligations.v`
- LINK-AMP (Sec 4.2, Fig.4) : `link_amplify` in `src/tlogic/LiveObligations.v`
- LINK-TRANS (Sec 4.2, Fig.4) : `link_trans` in `src/tlogic/LiveObligations.v`

#### Section 5
- sProp<sub>i</sub> (Sec 5, Fig.5): Definition `sProp` in `src/tlogic/LogicSyntaxHOAS.v`
- types &#964;(τ) in sProp<sub>i</sub> (Sec 5, Fig.5): `type` in `src/tlogic/TemporalLogic.v`
- type interpretation I of τ in sProp<sub>i</sub> (Sec 5, Fig.5): `type_interp` in `src/tlogic/TemporalLogic.v`
- type of predicates φ of sProp<sub>i</sub> (Sec 5, Fig.5): `sPropT` in `src/tlogic/TemporalLogic.v`
- atoms of sProp<sub>i</sub> (Sec 5, Fig.5): `Atom.t` (type t in Module Atom) in `src/tlogic/TemporalLogic.v` (also includes additional constructors to facilitate the development)
- semantic interpretation ⟦⋅⟧ of sProp<sub>i</sub> (Sec 5, Fig.5): `SyntaxI.interp` in `src/tlogic/LogicSyntaxHOAS.v`
- stratified world satisfaction W<sub>i</sub> (Sec 5): `syn_wsat` in `src/tlogic/TemporalLogic.v`
- worlds satisfaction Ws<sub>n</sub> (Sec 5): `syn_wsats` in `src/tlogic/TemporalLogic.v`
- FUPD-DEF (Sec 5.3, Fig 6): `FUpd` in `src/ra/IndexedInvariants.v` and `syn_fupd` in `src/tlogic/TemporalLogic.v`
- INV-ALLOC (Sec 5.3, Fig.6): `FUpd_alloc` in `src/ra/IndexedInvariants.v`
- INV-OPEN (Sec 5.3, Fig.6): `FUpd_open` in `src/ra/IndexedInvariants.v`
- INV-CLOSE (Sec 5.3, Fig.6): `FUpd_open` in `src/ra/IndexedInvariants.v`

#### Section 6
- delayed promise (Sec 6, Fig.7): `thread_delayed_promise` in `src/tlogic/LiveObligations.v`
- activation token &#10710;(⧖) (Sec 6, Fig.7): `pending_obligation` in `src/tlogic/LiveObligations.v`
- activated token &#8904;(⋈) (Sec 6, Fig.7): `active_obligation` in `src/tlogic/LiveObligations.v`
- ACTIVATE (Sec 6, Fig.7): `pending_active` in `src/tlogic/LiveObligations.v`
- NOT-ACT (Sec 6, Fig.7): `pending_not_active` in `src/tlogic/LiveObligations.v`
- CRED-NEW2 (Sec 6, Fig.7): `alloc_obligation_fine` in `src/tlogic/LiveObligations.v`
- OMAP-ADD2 (Sec 6.2, Fig.3): `duty_add` in `src/tlogic/LiveObligations.v`
- OBLS-FULFILL2 (Sec 6, Fig.7): `duty_fulfill` in `src/tlogic/LiveObligations.v`
- DP-PERS (Sec 6, Fig.7): `Persistent_thread_delayed_promise` in `src/tlogic/LiveObligations.v`
- DP-GET (Sec 6, Fig.7): `duty_delayed_promise` in `src/tlogic/LiveObligations.v`
- DP-ACT (Sec 6, Fig.7): `activate_tpromise` in `src/tlogic/LiveObligations.v`
- PROM-DEF (Sec 6, Fig.7): `unfold_promise` in `src/tlogic/LiveObligations.v`
- YIELD-TGT2 (Sec 6, Fig.7): `wpsim_yieldR_gen_pending` in `src/tlogic/SimWeakest.v`

### Case Studies and Examples
##### In `src/example`
- MP and MP<sub>S</sub> (Sec 2, Sec 3): `Client01.v`
- Specification of spinlock (Sec 4): `SpinlockSpec0.v`
- INCR_B (Sec 4.3): `DoubleIncrTicket.v`
- SL-PASS (Sec 7.1): `pass_lock` in `SpinlockSpec0.v`
- Generalized spinlock specification and view shift rules (Sec 7.1): `Spinlock_lock_spec` and `update_isSpinlock` in `SpinlockSpecUpdate.v`
- Ticketlock (Sec 7.1): `TicketLock.v`
- INF-MP and INF-MP-SPEC (Sec 2.1, Sec 7.3): `Client04.v`
- LP (Sec 7.3): `ClientSpinlock2.v`
- SCH-ND (Sec 2.1, Sec 7.3): `Client05.v`
- `fos_ticketlock/` contains the Lilo version of the weak memory ticket lock example from Fair Operational Semantics.
##### In `src/example/treiber`
- HT-ST (Sec 7.2): `Treiber_push_spec` in `SpecHOCAP.v`
- Treiber-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
##### In `src/example/elimstack`
- HT-ST (Sec 7.2): `Elim_push_spec` in `SpecHOCAP.v`
- Elimination-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
