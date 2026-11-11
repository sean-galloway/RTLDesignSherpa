# TASK-024: the monbus error window gets its own SRAM on the Genesys 2 harness (`stream_err`), and the fabric-benchmark harness elaborates again

**Date:** 2026-11-10
**Priority:** P2
**Status:** CLOSED 2026-11-10 -- `stream_err` is a 64-bit 4 KB `sdpram_slave_axil_axil` on the mon bridge (connectivity `monbus_wr -> stream_err`, bridge respun); the error window is resolved by name (`bridge_windows.monbus_err_window()`), `comp_sram` is the trace window entire; fabric-benchmark's `fb_harness` elaborates again (stale `s_axil_err_*` pins gone, slot SLVERR). Gates: fb dv 16/16; stream bridges dv 8/8, build-mon 50 (err_window PASSED on the new SRAM), build-obs 46, build-perf 76, all 0 rerun, serial from clean. The Genesys 2 bitstreams are NOT rebuilt here -- the next board build picks the new window up; the host tools already follow the name.
**Owner:** stream
**Found by:** owner, 2026-11-10: "fix the stream and rapids FPGA harnesses for the missing ports. Also ensure the error packets go to their own SRAM and that the tests know where to look"

## Why

stream TASK-019 (2026-10-25) put `monbus_axil4_group_1wr` in STREAM: the
error-selected packets are written to memory, so the `stream_err` bridge slot
(the old error-FIFO read port) became a reserved SLVERR window and the error
records were carved out of `comp_sram`'s top 4 KB -- the only memory the
group's `monbus_wr` master could reach without a bridge respin. Two things
were left behind:

1. The error records share a memory with the trace: a host reading the trace
   has to stop 4 KB short, the capture-window arithmetic lives in
   `bridge_windows.py`, and a wrong `MON_GROUP_*_LIMIT` corrupts the other
   stream's records silently.
2. `projects/fpga-systems/Genesys2/fabric-benchmark/rtl/fb_harness.sv` kept
   connecting `s_axil_err_*` pins that `stream_top_ch8` no longer has. The
   harness did not elaborate from 2026-10-25 on; its `dv/tests` ran 6 failed /
   10 passed and nobody noticed (found by bridge TASK-024's consumer gate).

## What changed

**Genesys 2 stream harness** (`projects/fpga-systems/Genesys2/dma-ip/stream`):

- `rtl/bridges/configs/bridge_stream_mon_axil.toml`: the `stream_err` slave is
  64-bit (was 32), like `comp_sram`; the connectivity CSV lets `monbus_wr`
  reach it. A bridge respin (`bin/regen_bridges.sh`), the first since the slot
  was reserved.
- `rtl/stream_harness.sv`: `u_err_sram`, a `sdpram_slave_axil_axil` (64-bit,
  512 words = 4 KB = 170 records, `USE_WSTRB=0` as on `comp_sram`) behind the
  `s3_*` nets, in place of the SLVERR responder. The error window IS this
  slot; `comp_sram` is the trace window entire.
- `bin/bridge_windows.py`: `monbus_err_window()` returns `W("stream_err")`,
  `monbus_capture_window()` returns all of `comp_sram`; the 4 KB carve-out
  constant is gone. Everything downstream already resolved both windows by
  name (`stream_monitors.route_monbus`, `mon_err_window.probe_err_window`,
  `dump_monbus.py`, `StreamHarnessTB`, `MonbusGroupHarness.err_window`), so
  no test or tool changed where it looks -- only the name's value did.
- Comments and docstrings that said "top 4 KB of comp_sram" (harness, TOML,
  host tools, the two tests' docstrings), `docs/PORT_MAP.md`, and the STREAM
  FPGA System book (Sections 2.1 / 2.2, revision 1.6).

**fabric-benchmark** (`projects/fpga-systems/Genesys2/fabric-benchmark`):

- `rtl/fb_harness.sv`: the four stale `s_axil_err_*` connections removed; the
  `stream_err` slot is RESERVED with a SLVERR responder on both channels (the
  shape the stream harness had), replacing the write-only sink. No error SRAM
  here: this harness builds STREAM with `GEN_MON=0` / `USE_AXI_MONITORS=0`,
  there is no monitor egress to store, and the bridge slot is 32-bit. The
  header's address-map comment says so.

**rapids harnesses:** rapids TASK-045 (same day, same shape: a 4 KB SRAM
behind the error window, CSR readback, a test that routes Completions there).

## Gate

- Stream bridge regenerated; `rtl/bridges/dv/tests` `make clean-all && make
  run-all`; `build-mon`, `build-obs`, `build-perf` `dv/tests` `make clean-all
  && make run-all-func` (build-mon's `test_stream_mon_err_window` is the
  end-to-end proof: Completions land in the new window, count matches, none
  in the trace); `make lint` on build-mon.
- fabric-benchmark `dv/tests` `make clean-all && make run-all-func`: 16 / 16.

## Results log

### 2026-11-10

- fabric-benchmark `dv/tests` from `make clean-all`: **16 passed, 0 rerun**
  (was 6 failed / 10 passed on HEAD, every failure the `s_axil_err_*`
  PINNOTFOUND at elaboration).
- stream BUG-023 (the build-mon `err_window` cosim sharing `test_stream_mon`'s
  sim_build under xdist, found by bridge TASK-024's gate) fixed alongside;
  build-mon reran 50 passed, 0 rerun before the window moved.
- Stream bridge respin and the stream suites on the new window, run serially
  from `make clean-all` after the MC-005 phase 3 commit (6c03f7981): regen
  65 files (`bridge_stream_mon_axil`, `bridge_stream_mon_axil_mon`, their
  generated TBs and test), lint 0 errors; `rtl/bridges/dv/tests` **8 passed,
  0 rerun**; build-mon **50 passed, 1 skipped, 0 rerun** with
  `test_stream_mon_err_window` PASSED against the `stream_err` SRAM;
  build-obs **46 passed, 1 skipped, 0 rerun**; build-perf **76 passed, 0
  rerun**. The one skip in build-mon and build-obs is
  `test_stream_mon_perf[desc_perf]`, which skips by design while
  `USE_DESC_AXI_MONITOR=0` (set `DESC_AXI_MON=1` to run it).
