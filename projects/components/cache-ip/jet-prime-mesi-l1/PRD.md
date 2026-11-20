<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# jet-prime — Product Requirements

**Version:** 0.1 (2026-11-12)
**Status:** inherits every DECIDED row of [jet's PRD](../jet-mesi-l1/PRD.md)
(J1–J10) and, through it, amber's. This file carries only what jet-prime
adds. Unreleased: stays at one revision while the design is being thrashed
out.

## 1. Purpose

Make the lockup-free MESI L1 faster than OpenHW HPDcache on the house
single-cache rig without giving up anything jet proved: coherence, the ACE
snoop side, MonBus observation, golden-model parity, the FULL soak grid.
jet is frozen as the measured baseline; jet-prime carries the change.

## 2. Requirements jet-prime adds

| ID | Requirement | Status |
|---|---|---|
| JP1 | Cycles per transaction below HPDcache's at every depth 1..16 on `r64k_we64` and `r64k_we255` on the reference rig (same injector, memory, bridge, UART, 100 MHz). | met 2026-11-17 (step 5, bin 4, as a pair with injector 1 idle): `r64k_we64` 12.76 / 7.91 / 6.10 / 5.41 / 5.29 at depths 1 / 2 / 4 / 8 / 16 against HPDcache's 13.73 / 9.79 / 8.22 / 7.67 / 7.64; `r64k_we255` 13.17 / 9.31 / 8.65 / 8.53 / 8.51 against 13.65 / 11.04 / 10.53 / 10.51 / 10.51 (depth-1 margin 3.5 %); `r128k_we64` under at every depth too. Steps 2-3 took depths 4-16; step 5 took depths 1-2 ([delta 03](docs/delta/03_single_miss_path.md)). |
| JP2 | Resident hits stay at 1.0 cycle per transaction from depth 4; hit latency stays at jet's 3 cycles at depth 1. | held through step 5 (hit floor 3, hit rows 1.00 from depth 4 on bin 4); superseded by JP7. |
| JP3 | Several fills in flight per cache (one AXI ID per outstanding miss, R demuxed by ID); the response order contract (J4) unchanged. | built 2026-11-15 (step 2, `jet_prime_fill`; [delta 01](docs/delta/01_fill_engine.md)); the pair rig runs it at full depth since JP4. |
| JP4 | The pair fabric serializes per line, not globally: distinct lines proceed concurrently; same-line conflicts keep grant-after-completion. | built 2026-11-16 (step 3, `jet_prime_pair_fabric` rebuilt around a transaction table; completion = the requester's retire, carried by the new `coh_done` sideband; [delta 02](docs/delta/02_pair_fabric.md)). |
| JP5 | jet's FULL grid, pair-rig DV and `jet_control` formal (prove, prove-live, cover) stay green on the fork at every step; new concurrency gets its own pair-rig scenarios and a formal safety argument for JP4. | built 2026-11-17 (step 4): `formal/jet-prime/jet_prime_pair_fabric` -- 24 safety properties on the per-line rule, the pulse-to-retire lock, the memory read's ordering and every valid/ready pair the fabric drives, 19 covers, 10 mutations; it found and fixed two memory-AR defects (BUG-001). Steps 2 and 3 carried by `test_jet_prime_fill`, the control TB's concurrent/out-of-order pass and the pair-rig lockstep model's transaction-table layer; control formal: safety prove PASS on the step-3 flat; the liveness BMC (depth 192) was at step 151 at this commit, covers queued behind it. Step 5 (control + fill engine changed): the control flat regenerated and its environment updated; the step-3 flat's liveness BMC (depth 192) PASS 2026-11-18 (19 h); covers on the step-5 flat PASS 2026-11-18 (23/23 and 7/7 reached); the step-5 safety prove (BMC depth 64, boolector) PASS 2026-11-18 (26:52); the step-5 liveness prove (depth 192) running at TASK-001's close (step 115 of 192), stopped by the owner at step 123 on 2026-11-18 (no counterexample; the 16/24/80 bounds covered, the two 128-count bounds not) -- the tighter environment and the run on the TASK-002 flat are TASK-003 (open 2026-11-19) |
| JP6 | Genesys2 at 100 MHz with positive slack on the reference-rig build and the pair-rig build. | met: the single-core reference build (`ref_jetp_bringup`, `REF_CACHE_SEL=2`) at step 2 (bin 2, 8,559 LUT / 7,182 FF, WNS +0.532 ns; not rebuilt since -- every later step measured as the pair) and the pair build (`ref_jetpp_bringup`, `REF_CACHE_SEL=3`) at every step since 3: bins 3-7 all met under the 0.2 ns clock-uncertainty budget, bin 7 at HEAD 18,241 LUT / 11,896 FF, WNS +0.040 ns, the worst path the fill engine's staging read pointer into the data BRAM address throughout. |
| JP7 | Resident hit latency at HPDcache's floor: 2 cycles at the injector, the resident rows at or within 0.05 cycles per transaction of HPDcache at depths 1 and 2, the thrash rows no worse than step 5's. | met 2026-11-19 (TASK-002, bin 7): hit floor 2; depth 1 `r4k_we0` 3.00 / `r4k_we255` 3.03 / `smoke4k_we64` 3.02 / `r16k_we64` 3.17 against HPDcache's 3.00 / 3.00 / 3.07 / 3.20; depth 2 1.50 / 1.54 / 1.58 / 1.66 against 1.50 / 1.50 / 1.53 / 1.64; thrash depth-1 margins 10.7 / 7.1 / 11.3 %, depths 4-16 equal to step 5 within 0.02 ([delta 04](docs/delta/04_two_cycle_hit.md)). |

## 3. Non-goals

- Changing the shared common-ip core (`l1_*`); if a step needs it, it is a
  common-ip task with its own scope confirmation.
- Beating HPDcache on area. jet-prime carries a snoop side and monitors the
  references do not; the area row is reported, not targeted.
- Touching jet. Its lanes are closed and its numbers are the baseline.
