# TASK-006: 75 MHz -- peregrine_top closes 13.333 ns on xc7a100t-1

**Priority:** P2
**Status:** closed 2026-11-26
**Owner:** Claude (owner decision 2026-11-26: "the slowest clock I want is 75mhz")

## Why

HIVE runs every domain at 75 MHz (HIVE PRD v0.3, owner 2026-11-26), and
peregrine closed at 54.1 MHz (PRD P14, TASK-001 stage 7). The owner set
75 MHz as the floor and accepted the CPI cost of the route below,
reversing the stage-7 choice to keep the CPI and lower the clock.

## Study (2026-11-25, OOC xc7a100t-1, 0.2 ns setup uncertainty)

HEAD at 13.333 ns: WNS -2.501. Every failing group runs through amber:
amber control state -> data RAM address (-2.50), `mie` -> interrupt
decision -> D request valid -> amber accept cone (-2.35), amber response
-> load align -> WB->EX forward -> ALU (-1.94). Core-only groups passed.

| build | WNS @ 13.333 |
|---|---|
| HEAD | -2.501 |
| + no WB->EX load forward | -2.003 |
| + registered interrupt decision | -0.525 |
| + amber miss reads beat 0 a cycle later | -0.305 |
| + amber clean-commit compare from a flop | +0.587 (+0.410 @ 13.0, -0.144 @ 12.5) |
| 2-cycle amber hit stand-in (the alternative) | +0.300 |

Time per instruction on the kernels: 24.8 ns today (1.343 CPI @ 54.1),
19.1 ns with the four changes (1.429 @ 75), about 20 ns with a 2-cycle hit.

## What

1. peregrine: no load forwarded WB->EX. `stall_ldbr` covers every ID
   consumer of a load in MEM; the EX MEM/WB arm is `mem_wb_q.alu_y`.
   Load-use: 2 bubbles. Kernels +6.4% CPI, rv32ui +0.4%.
2. peregrine: `peregrine_csr` registers `irq_pending` / `irq_cause`,
   cleared for one cycle by a CSR write, trap entry or mret. Interrupt
   recognition is one cycle later.
3. amber (common-ip `l1_control`, `DATA_SYNC_READ=1` only): the miss
   gather presents beat 0 in MISS_VICTIM's first cycle instead of LOOKUP
   switching the address on its next-state decode; a dirty miss is one
   cycle longer. Closes amber TASK-007's control-state -> data RAM path.
4. amber: CLEAN_COMMIT's still-M check is sampled in MISS_DRAIN (its only
   predecessor, which writes no tag) and registered. No cycle cost.
5. amber: the port-A tag / data address muxes and the compare-tag mux
   select on `acc_ok` (ready, a register function), not on `acc`. Found
   on the real RTL: one `MUL_DSP=1` placement missed by 0.003 ns on amber
   state -> ready -> the CPU's request valid -> `acc` -> tag LUTRAM
   address -> compare -> `state_d`. No cycle cost: port A is consumed in an
   accepting state only under `acc`.

## Done when

- peregrine FULL (incl. `RSP_SCRAMBLE`, irq, CPI harness), amber FULL,
  common-ip FULL, jet / jet-prime / onyx gates and amber control formal
  (prove, live, cover) green.
- amber TASK-005 latency test: read hit 1 / 1, write hit 1 / 2.
- OOC re-measured on the committed RTL at 13.333 ns and a step either side;
  PRD P14 set to 13.333 ns; MAS / PRD text updated for the load-use and
  interrupt timing.

## Result (2026-11-26)

- peregrine FULL 88/88, amber FULL 121/121, common-ip FULL 255/255, no
  reruns (clean-all first). jet / jet-prime / onyx: no filelist of theirs
  includes `l1_control`, so not affected and not run.
- amber control formal on the regenerated flat: prove (BMC 48), live
  (126) and cover all PASS.
- CPI harness: every program's cycle count equals the option (c) study
  (kernels 1.429, rv32ui 1.998); the miss lead cycle and the registered
  interrupt decision cost nothing measurable there.
- OOC on the committed RTL (0.2 ns uncertainty in):

  | period | `MUL_DSP=0` | `MUL_DSP=1` |
  |---|---|---|
  | 13.333 | +0.300 | +0.099 |
  | 13.0 | +0.316 | +0.111 |
  | 12.5 | +0.133 | |

  Limiter in every build: core `ex_mem` valid -> D request valid ->
  amber fast-path `state_d` (15 levels). 4,810 LUT / 3,009 FF / 9 BRAM
  (`MUL_DSP=0`).
- PRD P14, HAS ch05, MAS (hazards, CSR, traps, M unit, overview, core),
  the simplified book (ch02, ch04, ch05, ch07, index) and amber's MAS
  (ch02 blocks 01 / 03) updated; peregrine books rebuilt at v0.1.
