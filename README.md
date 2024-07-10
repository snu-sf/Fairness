# Lilo
This artifact contains Coq development for the paper *Lilo: A higher-order, relational concurrent separation logic
for liveness*.
- `Lilo-source.zip` contains source code.
- `Lilo.zip` contains a docker image (`Lilo.tar`) where you can find the pre-compiled Coq development.
Use following commands to run the image:
```
sudo docker load < Lilo.tar
docker run -it Lilo /bin/bash
cd Lilo # in the container
```

## Build
Requirement: opam (>=2.0.0), Coq 8.15.0
- Install dependencies with opam
```
./configure
```
- Build the project
```
make build -j
```

## Code Structure
### Definitions
#### Section 3
##### In `src/tlogic`
- obligation map (Obls<sub>i</sub>(Φ)) (Sec 3.2, Fig.1): `duty` in `LiveObligations.v`
- OMAP-ADD (Sec 3.2, Fig.1): `duty_add` in `LiveObligations.v`
- OMAP-FULFILL (Sec 3.2, Fig.1): `duty_fulfill` in `LiveObligations.v`
- progress credits (◇) (Sec 3.2, Fig.1): `progress_credit` in `LiveObligations.v`
- PC-SPLIT (Sec 3.2, Fig.1): `pc_split` in `LiveObligations.v`
- PC-DROP (Sec 3.2, Fig.1): `pc_drop` in `LiveObligations.v`
- thread promise (Sec 3.2, Fig.1): `thread_promise` in `LiveObligations.v`
- PROM-GET (Sec 3.2, Fig.1): `duty_tpromise` in `LiveObligations.v`
- PROM-PROGRESS (Sec 3.2, Fig.1): `tpromise_progress` in `LiveObligations.v`
- PROM-IND (Sec 3.2, Fig.1): `tpromise_ind` in `LiveObligations.v`
- simulation relation (Sec 3.3, Fig.2): `wpsim` in `SimWeakest.v`
- INV-ALLOC (Sec 3.3, Fig.2): `FUpd_alloc` in `IndexedInvariants.v`
- INV-OPEN (Sec 3.3, Fig.2): `FUpd_open` in `IndexedInvariants.v`
- INV-CLOSE (Sec 3.3, Fig.2): `FUpd_open` in `IndexedInvariants.v`
- SIM-PAR (Sec 3.3, Fig.2): `whole_sim` in `SimWeakestAdequacy.v`
- SIM-TERM (Sec 3.3, Fig.2): `wpsim_ret` in `SimWeakest.v`
##### In `src/example`
- MEM-READ (Sec 3.3, Fig.2): `SCMem_load_fun_spec` in `SCMemSpec.v`
- MEM-WRITE (Sec 3.3, Fig.2): `SCMem_store_fun_spec` in `SCMemSpec.v`

#### Section 4
##### In `src/tlogic`
- liveness obligation (◆<sub>k</sub>⌈ℓ, n⌉) (Sec 4.2, Fig.3): `liveness_obligation_fine` in `LiveObligations.v`
- OBL-NEW (Sec 4.2, Fig.3): `alloc_obligation_fine` in `LiveObligations.v`
- OBL-NEW (Sec 4.2, Fig.3): `lo_ind_fine` in `LiveObligations.v`
- obligation link (◆<sub>k</sub>⌈ℓ, n⌉) (Sec 4.2, Fig.3): `link` in `LiveObligations.v`
- LINK-NEW (Sec 4.2, Fig.3): `link_new_fine` in `LiveObligations.v`
- LINK-AMP (Sec 4.2, Fig.3): `link_amplify` in `LiveObligations.v`
- LINK-TRANS (Sec 4.2, Fig.3): `link_trans` in `LiveObligations.v`

#### Section 5
##### In `src/tlogic`
- sProp<sub>i</sub> (Sec 5.1, Fig.4): `sProp` in `LogicSyntaxHOAS.v`
- types &#964;(τ) in sProp<sub>i</sub> (Sec 5.1, Fig.4): `type` in `TemporalLogic.v`
- type interpretation 𝓘 of τ in sProp<sub>i</sub> (Sec 5.1, Fig.4): `type_interp` in `TemporalLogic.v`
- special type φ of sProp<sub>i</sub> (Sec 5.1, Fig.4): `sPropT` in `TemporalLogic.v`
- semantic interpretation ⟦⋅⟧ of sProp<sub>i</sub> (Sec 5.1, Fig.4): `SyntaxI.interp` in `LogicSyntaxHOAS.v`
- stratified world satisfaction W<sub>i</sub> (Sec 5.2): `syn_wsat` in `TemporalLogic.v`
- fancy update modality (Sec 5.3, Fig.5): `FUpd` in `IndexedInvariants.v`
- INV-ALLOC' (Sec 3.3, Fig.2): `FUpd_alloc` in `IndexedInvariants.v`
- INV-OPEN' (Sec 5.3, Fig.5): `FUpd_open` in `IndexedInvariants.v`
- INV-CLOSE' (Sec 5.3, Fig.5): `FUpd_open` in `IndexedInvariants.v`

#### Section 6
##### In `src/tlogic`
- delayed promise (Sec 6.1, Fig.6): `delayed_tpromise` in `LiveObligations.v`
- activation token &#10710;(⧖) (Sec 6.1, Fig.6): `pending_obligation` in `LiveObligations.v`
- activated token &#8904;(⋈) (Sec 6.1, Fig.6): `active_obligation` in `LiveObligations.v`
- ACTIVATE (Sec 6.1, Fig.6): `pending_active` in `LiveObligations.v`
- NOT-ACT (Sec 6.1, Fig.6): `pending_not_active` in `LiveObligations.v`
- DP-ACT (Sec 6.1, Fig.6): `activate_tpromise` in `LiveObligations.v`
- YIELD-TGT2 (Sec 6.1, Fig.6): `wpsim_yieldR_gen_pending` in `SimWeakest.v`

#### Section 7
##### In `src/example`
<!-- - SL-UPDATE (Sec 7.1): `update_isSpinlock` in `SpinlockSpecUpdate.v` -->
- SL-PASS (Sec 7.1): `pass_lock` in `SpinlockSpec0.v`
##### In `src/example/treiber`
- HT-ST (Sec 7.2): `Treiber_push_spec` in `SpecHOCAP.v`
##### In `src/example/elimstack`
- HT-ST (Sec 7.2): `Elim_push_spec` in `SpecHOCAP.v`
  
### Theorems
##### In `src/tlogic`
- Theorem 6.1 (Adequacy): `Theorem whole_sim_implies_refinement` in `SimWeakestAdequacy.v`

### Examples
##### In `src/example`
- INF-MP and INF-MP-SPEC (Sec 2, Sec 7): `Client04.v`
- MP and MP<sub>S</sub> (Sec 2, Sec 3): `Client01.v`
- SCH-ND and SCH-ND-SPEC (Sec 2, Sec 7): `Client05.v`
- Ticketlock (Sec 7.1): `TicketLock.v`
- LP and LP-SPEC (Sec 7.3): `ClientSpinlock2.v`
##### In `src/example/treiber`
- Treiber-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`
##### In `src/example/elimstack`
- Elimination-Stack (Sec 7.2): `SpecHOCAP.v`
- STACK-MP (Sec 7.2): `ClientSpecHOCAP.v`