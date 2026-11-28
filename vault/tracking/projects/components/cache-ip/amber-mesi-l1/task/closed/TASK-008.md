# TASK-008: bus error reporting on the CPU port (failed fill) and a sticky write-back error

**Priority:** P3
**Status:** closed 2026-11-27 (filed 2026-11-27 from riscv-ip/peregrine-rv32im TASK-005, owner decisions 2026-11-27)
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im TASK-005)

## Why

peregrine (riscv-ip/peregrine-rv32im TASK-005) takes load and store access
faults on an AXI SLVERR / DECERR. Its D$ is amber, and amber ignored
`rresp` and `bresp`: a fill that came back with an error installed the bad
beats as a valid line, and a write-back that failed was forgotten. Owner
decisions (2026-11-27):

- a failed FILL is reported on the CPU response, so the core can take a
  precise access fault on the instruction that missed;
- a failed WRITE-BACK of a dirty line has no instruction to blame: amber
  DROPS the line, latches the failing address in a status register, and
  raises an interrupt (an imprecise error report).

## What

- `BUS_ERR_EN` (amber_top, l1_coh_core, l1_control, l1_cpu_plane, and the
  shared l1_cpu_frontend's `RSP_ERR_EN`), default 0: every existing
  consumer elaborates exactly what it did before. peregrine sets 1.
- Failed fill (any R beat with `rresp[1]` set): nothing is installed. A true
  fill writes the victim way Invalid at FILL_WRITE (its data was
  overwritten by the bad beats); an upgrade (CleanUnique) leaves the line in
  its installed state. The request is then answered at once, without the
  replay, with the error bit set: the response is one bit wider
  (`cpu_rsp_rd_data[BUS_WIDTH]`). The answer reuses CLEAN_RSP (16 one-hot
  states, all in use), which responds from the latched context.
- Failed write-back (`bresp[1]`), eviction or clean-all: the line is
  dropped (an eviction already removed it; a clean-all's line is written
  Invalid at CLEAN_COMMIT instead of E, so the walk still ends). The line
  address is latched in `wb_err_addr`, `wb_err_valid` rises and stays up
  until `wb_err_clear`; a second failure while it is up sets
  `wb_err_ovf` and keeps the first address.
- OKAY responses: bit-for-bit the same behaviour (the error terms are
  AND-ed with the response code, and compiled out at `BUS_ERR_EN=0`).

## Done when

- amber's own suite has a directed test of each path (failed read fill,
  failed write-allocate fill, failed eviction write-back, failed clean-all
  write-back, the overflow bit, and the clear), and a mutant dropping each
  is caught.
- amber FULL, common-ip FULL and the amber formal suite are green; jet and
  jet-prime (which share l1_cpu_frontend) are green.
- amber's MAS describes the error path.

## As built (2026-11-27)

- Detection in `l1_coh_core` on the engine seam (`fub_axi_rvalid &
  rready & rresp[1]`, `bvalid & bready & bresp[1]`); `l1_fill` /
  `l1_drain` untouched. `l1_control` gains `ctrl_fill_err`,
  `ctrl_drain_err`, `ctrl_rsp_err` (every harness ties them off).
- Error response: `CTRL_FILL_WRITE` -> `CTRL_CLEAN_RSP` with `rsp_err_q`;
  `l1_cpu_frontend` `RSP_ERR_EN` widens its staging FIFO by the bit
  (default 0: jet / jet-prime elaborate as before).
- Sticky status `wb_err_{valid, addr, ovf}` in `l1_coh_core`, address
  from the drain's own AW; clear wins over a held error, a new error in
  the clear's cycle is latched fresh.
- DV: `test_amber_buserr` (amber_top `BUS_ERR_EN=1`, house AXI4 / GAXI
  BFMs, READ_FILL_E 0/1 x gate/func/full): failed read fill, refetch,
  victim invalidated, failed write-allocate, failed CleanUnique upgrade
  (READ_FILL_E=0), eviction WB error, overflow, clear, clean-all with two
  failed WriteCleans and a good one, and 1500 / 8000 OKAY ops against a
  scoreboard. Mutants: fill error dropped and write-back error dropped are
  caught here and in peregrine's suite.
- amber FULL 127/127, common-ip FULL 255/255; amber_control formal
  (flat regenerated, `--param BUS_ERR_EN=0`): prove, live, cover PASS.
- OOC amber_top xc7a100t-1 13.333 ns, 0.2 ns uncertainty, `MAINT_EN=1
  USE_MONITOR=0 READ_FILL_E=1`: `BUS_ERR_EN=1` +0.242, HEAD +0.175
  (limiter the snoop CRRESP path in both, untouched).
- jet-prime FULL 155/155. jet FULL 148/149: the one failure
  (`test_jet_pair_rig` fifo_mon_full, scenario (j) tag budget) fails the
  same way on the archived HEAD tree at the same seed (90573), so it is
  jet's and not this change's.
- Known limit, documented in the MAS: at `BUS_ERR_EN=1` a snoop answered
  during a fill that later fails is given that fill's data; acceptable for
  a cache with no coherent peer (peregrine).
