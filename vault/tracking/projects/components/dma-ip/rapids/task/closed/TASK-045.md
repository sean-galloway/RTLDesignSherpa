# TASK-045: the monbus error window gets its own SRAM on both Genesys 2 rapids harnesses, with CSR readback and a test that uses it

**Date:** 2026-11-10
**Priority:** P2
**Status:** CLOSED 2026-11-11 -- both Genesys 2 rapids harnesses capture the error window in their own 512 x 64 memory (AW/W pairing FIFO, nothing dropped), read back through `ERRCAP_SEL/LO/HI`, with `ERR_REC_CNT` and `ERR_WIN_BASE/LIMIT` CSRs; MON_CAPTURE is trace-only; `byte_sequences.monbus_err_window()` and `cocotb_test_err_window` in both flows (12 landed / 12 read back, all Completions). Gates: byte `make sim` 86 passed, beats dv 5 passed, 0 rerun, serial from clean. Monitor bitstreams rebuilt 2026-11-11 (byte `bitstream-mon` WNS +0.113 ns, beats monitors-on WNS +0.298 ns at 100 MHz, both met, neither board-run; below).
**Owner:** rapids
**Found by:** owner, 2026-11-10: "fix the stream and rapids FPGA harnesses for the missing ports. Also ensure the error packets go to their own SRAM and that the tests know where to look" (twin of stream TASK-024)

## Why

rapids TASK-039 (2026-10-25) put `monbus_axil4_group_1wr` on every RAPIDS top
and gave the two Genesys 2 harnesses (`flows-rapids/rtl/rapids_byte_harness.sv`,
`flows-rapids-beats/rtl/rapids_char_harness.sv`) the `cfg_mon_err_*` ports.
Both harnesses elaborate today (`make lint` clean on both before this change;
the "missing ports" of the day are fabric-benchmark's, stream TASK-024). What
they did with the error window was nothing: the monitor egress went to an
always-accept responder and was dropped, the window was declared as the 64 KB
above the trace window, "nothing on this harness reads it yet", and
`mon_err_rec_count` was left unconnected. The byte harness's `MON_CAPTURE`
buffer stored every egress beat, error records and trace alike, so the host's
error-packet check read the error records out of the trace capture.

## What changed (both harnesses, same code)

- **The error window is 4 KB** (`MON_LIMIT + 1 .. MON_LIMIT + 0x1000`, was
  64 KB) **with its own memory**: `r_ec_mem`, 512 x 64-bit, reset-free
  storage written at the beat (memory-controllers MC-005's rule), at word
  `(awaddr - base) >> 3` for every W beat whose AW address is in the window.
- **AW/W pairing.** The responder accepted AW and W independently; the capture
  needs the address before it can place the beat. A `gaxi_fifo_sync` (depth
  8) queues `{in-window, word index}` per accepted AW, each accepted W pops
  one; W waits while the queue is empty, AW waits while it is full. Legal AXI
  backpressure, nothing dropped, the egress paced by its own AW; the B
  counters are unchanged.
- **CSRs** (both regmaps, `bin/gen_rapids_harness_regmap.py`, regenerated):
  `ERRCAP_SEL` 0x0E4 (word index), `ERRCAP_LO` 0x0E8, `ERRCAP_HI` 0x0EC,
  `ERR_REC_CNT` 0x0F0 (the DUT's `mon_err_rec_count`, now connected),
  `ERR_WIN_BASE` 0x0F4, `ERR_WIN_LIMIT` 0x0F8 (the window as driven, so no
  host retypes the arithmetic). The MONCAP shape.
- **Byte harness `MON_CAPTURE`** stores the trace window only (error-window
  beats are excluded), so the two routes are exclusive in what the host reads.
- **Host / tests.** `flows-rapids/host/byte_sequences.py`:
  `monbus_err_window(s)` reads the window via the CSRs and decodes it with
  the shared parser; `_check_monbus_error_packet` checks the error window
  first (every counted record parses) before its by-design skip on the trace.
  New `cocotb_test_err_window` in both flows' harness tests, built with
  `USE_AXI_MONITORS=1 GEN_MON=1` (the byte one also `MON_CAPTURE=1`): the SRC
  half's `WRMON_ERR_CFG.ERR_SELECT` routes Completions to the error window
  (that register IS the group's core-protocol select, `rapids_top_base`),
  a sink self-check runs, `ERR_REC_CNT` must advance, every counted slot must
  read back as a Completion, and (byte) the trace capture must hold none.
  `_run_harness` gains the `TEST_USE_AXI_MONITORS` (and, beats,
  `TEST_GEN_MON`) build knobs.

## Gate

- `make lint` on both flows (declaration order, call-select, Verilator).
- The two new tests, plus each flow's existing harness suite from a clean
  build (`make sim` in `flows-rapids`; the beats `dv/` pytest).

## Results log

### 2026-11-10

- `make lint` clean on both flows before and after the change.
- The first run of both new tests failed on my own check, not the hardware:
  I compared `ERR_WIN_BASE` against `MON_LIMIT + 1`, and `MON_LIMIT` is a
  write-only CSR in both harnesses (no read-mux entry, reads 0). The window
  itself read back 0x0000_5000..0x0000_5FFF, the 4 KB above the trace window
  the campaign programs. The check now uses the two window registers alone,
  which is what they are for.
- `test_rapids_byte_harness_err_window` (USE_AXI_MONITORS=1 GEN_MON=1
  MON_CAPTURE=1): 12 Completion records landed, 12 read back from the SRAM
  through `ERRCAP_*`, every one a Completion, and the trace capture held 0
  records -- the sink self-check's core emitters produced Completions only,
  so the exclusivity half of the check had nothing to reject; a run with a
  second class unmasked would make it bite.
- `test_rapids_char_harness_err_window` (USE_AXI_MONITORS=1 GEN_MON=1): 12
  landed, 12 read back, all Completions.
- Both flows' harness suites from clean builds (`local_sim_build` removed),
  run serially after the stream suites: byte flow `make sim` **86 passed, 0
  rerun** (11 h 52 min; `test_rapids_byte_harness_err_window` PASSED among
  them); beats flow `pytest dv` **5 passed, 0 rerun** (29 min, err_window
  included).

## Bitstream rebuild (2026-11-11, owner: "build for completeness")

The monitor variants, the ones in which the error window exists (`GEN_MON=1`),
rebuilt serially after the stream build; each flow's `verify-sim` gate passed
first.

| build | result |
|---|---|
| byte `make bitstream-mon` (USE_AXI_MONITORS=1 GEN_MON=1 MON_CAPTURE=1, 8ch, 256-bit) | 13 min; `bitstream/rapids_byte_mon.bit`, metrics in `reports/build/metrics_mon.json`; all constraints met, **WNS +0.113 ns** / WHS +0.059 ns at 100 MHz; 77,376 LUT / 59,438 FF / 82.5 BRAM |
| beats `make bitstream BOARD=genesys2 USE_AXI_MONITORS=1 GEN_MON=1` | 18 min; `bitstream/rapids_char.bit`, copied to `rapids_char_mon.bit` by the area's naming habit; all constraints met, WNS +0.298 ns / WHS +0.055 ns at 100 MHz; 76,493 LUT / 73,210 FF / 44.5 BRAM |

Neither was programmed or board-run (the Genesys 2 is STREAM's; rapids board
runs were waived in TASK-039).

The plain variants followed on the owner's "both" (2026-11-11), serially,
verify-sim first; all met, none board-run:

| build | result |
|---|---|
| byte `bitstream-std` | `rapids_byte_std.bit`, WNS +0.580 / WHS +0.033 ns, 65,291 LUT |
| byte `bitstream-perf` | `rapids_byte_perf.bit`, WNS +0.440 / WHS +0.059 ns, 58,510 LUT |
| beats `bitstream BOARD=genesys2` (monitors off) | `rapids_char.bit`, WNS +0.449 / WHS +0.046 ns, 56,514 LUT |

**Timing margin flag.** Neither rapids rig constrains clock uncertainty (no
`set_clock_uncertainty` in either XDC), so the byte mon build's +0.113 ns is
inside the ~0.2 ns placement spread the owner budgets elsewhere
(cache-ip rigs, 1322ff59c): it met, but not predictably. Whether to add the
budget to the rapids XDCs (and then fix structurally what fails) is a
separate decision; nothing in this task changed the critical path by design.
