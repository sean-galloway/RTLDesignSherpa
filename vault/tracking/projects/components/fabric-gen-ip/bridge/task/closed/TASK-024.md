# TASK-024: the generated FIFO storage arrays out of `ALWAYS_FF_RST` into their own clock-only process (memory-controllers MC-005 phase 3)

**Date:** 2026-11-10
**Priority:** P2
**Status:** CLOSED 2026-11-10 -- generator patched, every bridge in the repo regenerated (532 generated .sv across the bridge batch and nine fpga-systems areas), mechanical check passed, every suite green from a clean build, the two ECC loop UART sims included (bch 14, reed-solomon 18; finished the same evening after a part-way deferral); Synth 8-4767 bridge arrays 17 -> 0 on both controllers (below).
**Owner:** bridge
**Where:** `bin/bridge_pkg/emit_utils.py` (`mem_write_lines`), `bin/bridge_pkg/generators/{crossbar,slave_adapter,adapter}_generator.py`; every `rtl/bridges/generated/` tree the generator feeds
**Found by:** memory-controllers ISSUE-001 (the FPGA microarchitecture review, 2026-11-05), resolution row 2b; MC-005 phases 1 and 2 cleared the hand-written arrays on 2026-11-06 and left 17 per controller, all bridge-generated

## Why

Vivado will not infer distributed or block RAM from an array written in a
process that has an asynchronous reset branch, whatever that branch does to
the array (`[Synth 8-4767] ... RAM is sensitive to asynchronous reset
signal`); the array dissolves into flops plus a read mux. The repo macro
`ALWAYS_FF_RST` is unconditionally async-assert, and the generator wrote
every one of its FIFO storage arrays inside it, beside the pointers the
branch resets. After MC-005 phases 1 and 2 the pumice and granite
characterization builds each still reported 17 such arrays, every one in
generated bridge RTL: the seven APB adapters' `wr_fifo` / `rd_fifo`
(B / R routing by position), the host adapter's `w_trk_mem` (AW to W
slave select) and the crossbar's `host_64b/32b_wdest_mem` (W destination
per master path). Two more families are emitted only by configurations
those two boards do not use and were not in the review's list: the
crossbar's slave-side W owner FIFO (`<slave>_wowner_mem`, both the shim
and the owner-bypass variant) and the master adapter's local read-return
atomic queue (`lr_mem`, `atomic_rr` configurations).

The rule and the method are `vault/handbook/design/sram-and-memories.md`,
"An unreset array inside a reset block still synthesizes as flops"; the
census and the gate are memory-controllers MC-005.

## What changed (generator)

One helper, `emit_utils.mem_write_lines(write_stmt, cond)`, emits the
storage array's own process:

    // storage array: clock-only process, no reset (Synth 8-4767 -- see
    // vault/handbook/design/sram-and-memories.md)
    always_ff @(posedge aclk) begin
        if (<push condition>) <array>[<wptr slice>] <= <value>;
    end

Each of the six emission sites drops the array write from its
`ALWAYS_FF_RST` block (the pointers, their reset and their advance stay
exactly as they were) and appends that process with the SAME condition and
the SAME index expression:

| site | array | condition |
|---|---|---|
| `crossbar_generator` W destination FIFO | `<master>_<w>_wdest_mem` | `<base>_push` |
| `crossbar_generator` W owner FIFO, shim slaves | `<slave>_wowner_mem` | `<slave>awvalid && awready` |
| `crossbar_generator` W owner FIFO, owner bypass | `<slave>_wowner_mem` | `aw_hs && !ahead && !(byp && w_end)` -- the `else if` branch that advanced `wptr`, written out |
| `slave_adapter_generator` write channel | `wr_fifo` | `<xbar>awvalid && awready` |
| `slave_adapter_generator` read channel | `rd_fifo` | `<xbar>arvalid && arready` |
| `adapter_generator` AW to W tracking | `w_trk_mem` | `w_trk_push` |
| `adapter_generator` local atomic R queue | `lr_mem` | `awvalid && awready && aw_rr_local` |

Every reader of these arrays was already qualified by the pointers' valid
(`_valid && head == code`, `(wptr != rptr) ? mem[rptr] : '0`, `bid_valid` /
`rid_valid` gating the crossbar's response muxes, `r_local_head` for
`r_local_id`), and none of the arrays was in a reset branch's assignment
list, so the generated RTL is behaviour-identical in simulation; only the
synth log can tell. The per-ID trackers (`*_idt_cnt / _tgt / _trace`) are
reset per entry in a loop and stay where they are: they are counters, not
storage.

## Regeneration (CLAUDE.md Rule #0)

Before the change, every generated bridge was regenerated with the
unchanged generator to know the baseline: the bridge batch (75 bridges) and
ddr2_char_framework, jet, amber, stream, bridge-stress were byte-identical
to the tree; scoria, bch and reed-solomon were BEHIND the generator
(committed `SKID_DEPTH_W = 4` against the generator's 2, and no
`<bridge>_sizing.json`), and fabric-benchmark's three `_sizing.json` lacked
the `r_queue_depth` key. Those are earlier generator changes that were never
propagated; this regeneration carries them, and the commit says so.

After the change: `bin/make regen` + `bridge_generator.py --bulk
bridge_batch.csv --generate-tests` (the generated tests and TB classes come
out identical; the six test files the batch's `_1wr` entries would emit and
nobody ever committed were left out again), then each consumer's own
`bin/regen_bridges.sh` / `bin/regen.sh`. fabric-benchmark's
`fb_litex_xbar.v` changes only by the LiteX timestamp and is not taken.

**Mechanical check of the diff** (`git diff -U0` over the 532 changed
generated `.sv`, scripted): 1,118 array-write statements removed from
`ALWAYS_FF_RST` blocks and 1,118 added, each one verbatim under an `if
(<cond>)` in a new `always_ff @(posedge aclk)`; per file the removed and
added statement multisets are equal; no other `<=` line moved. The only
other lines in the diff are the helper's two comment lines, the process
open / close, and the six `SKID_DEPTH_W` 4 -> 2 lines of the three
already-behind consumers.

## Gate (run 2026-11-10, results in the table below)

- Generator unit tests: `bin/make test` 266 passed.
- Bridge DV: `dv/tests`, `make clean-all && make run-all-func` (serial).
- Every consumer DV suite that compiles a regenerated bridge, `clean-all`
  first: stream `rtl/bridges/dv/tests`, fabric-benchmark, bridge-stress,
  jet, amber, bch `build-loop`, reed-solomon `build-loop`, stream
  `build-mon` / `build-obs` / `build-perf`, ddr2_char_framework.
- Synth, the task's own check: granite sys100 and pumice sys75 `make synth`,
  `grep -c 'Synth 8-4767' vivado.log` must read 0 (17 each before), with
  the "LUT as Memory" and register counts recorded in MC-005.

## Gate results (2026-11-10, every suite from `make clean-all`)

| gate | result |
|---|---|
| generator unit tests (`bin/make test`) | 266 passed |
| bridge `dv/tests` `run-all-func` | 596 passed (52 min) |
| stream `rtl/bridges/dv/tests` `run-all` | 8 passed |
| fabric-benchmark `dv/tests` | 6 failed / 10 passed -- the harness, red on HEAD, not this change (below; fixed in stream TASK-024) |
| bridge-stress `dv/tests` | 61 passed |
| jet `dv/tests` | 4 passed |
| amber `dv/tests` | 4 passed |
| bch `build-loop` (`make sim`) | 14 passed (2 h 30 min). The owner deferred the ECC loops part-way on 2026-11-10 ("we can fix ecc later") and this row briefly read "11 passed when deferred"; the run had in fact finished (only its wrapper script was stopped) |
| reed-solomon `build-loop` (`make sim`) | 18 passed (1 h 22 min), rerun from clean 2026-11-10 evening on the owner's "handle the ecc now". The first run showed one F at `debug_walk` after 7 passed: that was the simulator killed by PID when the loops were deferred (pid in the session transcript), not a test failure; `debug_walk` passes on the rerun |
| stream `build-mon` | 50 passed, 1 skipped, 2 rerun (stream BUG-023, below); rerun after the fix 50 passed, 0 rerun |
| stream `build-obs` | 46 passed, 1 skipped |
| stream `build-perf` | 76 passed |
| ddr2_char_framework | 226 passed, 2 xfailed |
| synth granite sys100, `Synth 8-4767` | 18 -> **1** (the survivor is `mc_bank_fifo_store.r_wr_mgpos`, dead under `STORE_MERGE_EN = 0`; not a bridge array -- below) |
| synth pumice sys75, `Synth 8-4767` | 17 -> **0** |
| synth A/B, same tree (HEAD + the peer's uncommitted FIFO-attribute edit in both) | granite -32 LUT / +12 LUTRAM / **-176 FF**; pumice -32 / +12 / **-176** -- the full table is in MC-005 |

## Results log

### 2026-11-10: two suite results that are not this change

- **fabric-benchmark `dv/tests`: 6 failed / 10 passed, every failure the same
  elaboration error** -- `rtl/fb_harness.sv:666-669` connects
  `s_axil_err_*` pins that `stream_top_ch8` no longer has (the STREAM error
  AXI-Lite port went with the write-only monbus group on 2026-10-25; the
  harness was last edited 2026-10-31 and still names them). Neither file is
  touched here and no bridge is involved; the suite was already red on HEAD.
  fabric-benchmark has no tracker lane of its own, so it is recorded here and
  reported to the owner.
- **stream `rtl/bridges/dv/tests`** has its own Makefile (`run` /
  `run-all`, not the shared `run-all-func`); the first attempt hit the wrong
  target and the suite was rerun with `make run-all`.
- **stream `build-mon`: 50 passed, 1 skipped, 2 rerun** -- both reruns
  `test_stream_mon_err_window`, which the runner mapped to the base test's
  sim_build and log name and so built the same tree as `test_stream_mon` in
  the same directory under xdist (two 0-byte results files at the attempt
  times, no log). A test-infrastructure defect, nothing in the sim differs
  between attempts: filed and fixed as stream BUG-023 (its own sim_build
  name), suite rerun clean below. No bridge involved.
- **granite synth: `Synth 8-4767` reads 1, not 0** -- `r_wr_mgpos_reg` in
  `mc_bank_fifo_store`, reason "No valid read/write found for RAM", not the
  async-reset reason. That array was moved out of the reset block in MC-005
  phase 1 and inferred cleanly on 11-07; the FPGA SKU has had
  `STORE_MERGE_EN = 0` since MC-006 (2026-11-07), under which its only write
  (`w_aw_merge`) is constant 0, so Vivado dissolves a never-written array
  and trims it. It is in the 11-08 budget-build logs already, costs
  nothing, and is not a bridge array: the 17 bridge-generated arrays are
  0 on both controllers. Recorded in MC-005 as the residual.
