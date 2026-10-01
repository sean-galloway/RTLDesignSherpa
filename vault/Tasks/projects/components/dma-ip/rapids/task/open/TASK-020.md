# TASK-020: AXI response-error injection in the byte-RAPIDS Genesys 2 harness

**Priority:** P2 -- the byte-perf report states that RRESP/BRESP error
handling is not exercised on silicon; it is the one gap left in the
byte-RAPIDS characterization.
**Status:** ACTIVE 2026-10-01. Proven on silicon -- 36/36 checks on the board.
The ONLY thing left is the monbus error-PACKET check, which needs a
monbus-buffer readout the host does not have (see "What the monbus box still
needs"). Everything else in this task is done.
**Owner:** TBD

The harness memory model always answers OKAY, and the harness has no hook to
change that, so the sink's B-response error path and the source's R-response
error path are covered only in the unit and macro sims.

## Done when

- [x] a harness CSR (by name, through the generated regmap) selects an error
      response for a chosen transaction on R and on B (CSR_ERR_INJ /
      CSR_ERR_STAT, 2026-09-30; see "Design as built")
- [ ] directed sequences drive RRESP=SLVERR and BRESP=SLVERR and check the
      channel error status, the monbus error packet, and recovery through
      channel reset -- written (`axi_resp_error`) and covering the error
      status and channel-reset recovery; the MONBUS PACKET half is not done
      and needs a readout that does not exist yet (see below)
- [x] the sequences pass in the UART sim harness before any board run
      (2026-10-01, 18/18 checks at gate)
- [x] a new bitstream is built, proven on the board, and the byte perf
      report lists the error rows (2026-10-01: 36/36 on the board at
      `--seq-level full`, perf report section 8.1)

## Design as built (2026-09-30)

The two synthetic AXI slaves in `rtl/amba/shared/` are where a response is
manufactured, and both hardwired OKAY (`axi4_slave_wr_crc_check.sv` BRESP,
`axi4_slave_rd_pattern_gen.sv` RRESP). They are SHARED with STREAM's harness
and the RAPIDS-beats harness, so the hook follows the `BYTE_CRC` precedent:
a `parameter bit ERR_INJECT = 1'b0` whose 0 case elaborates none of the logic
and holds the response at OKAY. Every other consumer keeps today's behaviour
with a tie-off and no parameter change.

- **Both slaves** gain `ERR_INJECT` plus five config inputs and one status
  output: `cfg_err_enable`, `cfg_err_channel`, `cfg_err_skip[15:0]`,
  `cfg_err_resp[1:0]`, `cfg_err_oneshot`, `err_injected` (sticky). Armed, the
  slave counts bursts on the selected channel and the one whose index equals
  `cfg_err_skip` answers `cfg_err_resp`; one-shot disarms after it so a
  sequence can prove recovery on the next burst.
- **Write side:** the response travels WITH its burst through the existing
  16-deep B FIFO (a parallel `r_bfifo_resp` array), not muxed onto whatever B
  is presented -- with several bursts outstanding those are different things
  and only the former is addressable from a test.
- **Read side:** the decision is latched at AR acceptance, so it follows that
  burst even though `arready` accepts the next AR on the last R beat. Every
  beat of the chosen burst carries the error.
- **`axi4_dma_slaves`** (the wrapper STREAM's harness uses) ties both leaves'
  config off internally and exposes nothing new, so `stream_harness.sv` needed
  no edit at all. Promote the ports when a consumer of the wrapper wants them.
- **The beats harness** (`rapids_char_harness.sv`) gets tie-off lines only and
  keeps `ERR_INJECT` at 0 -- the TASK-019 constraint that RAPIDS Beats neither
  loses nor gains behaviour.
- **The byte harness** builds both slaves with `ERR_INJECT=1` and adds
  `CSR_ERR_INJ` (0x0C8: WR_EN, RD_EN, RESP, CH, ONESHOT, SKIP) and
  `CSR_ERR_STAT` (0x0CC: WR_HIT, RD_HIT, read-only, straight from the slaves).
  Both are in the regenerated `rapids_harness_csr_regmap.py` (66 regs), so the
  host drives them BY NAME.
- **Host:** `byte_sequences.py` gains `axi_resp_error`, registered in the sim
  campaign's `SEQS`. Per half it arms one SLVERR burst on ch0 while ch1 runs
  alongside, then checks the slave really issued it (`ERR_STAT`, measured at
  the slave, so a passing status check cannot be the DUT agreeing with
  itself), the DUT's sticky per-channel flag on the TARGETED channel only
  (`SNK_SCHERR`/`SRC_SCHERR` + `SCHED_ERROR`), that `CHANNEL_RESET` clears it,
  and that the channel is golden afterwards.

The DUT side needed no change: `axi_write_engine.sv` already sets a sticky
per-channel `r_wr_error` on any non-OKAY B, `axi_read_engine.sv` the same on
`r_rd_error` for R, and both clear only on `cfg_channel_reset` or `aresetn`.
What was missing was never the error path -- it was any way to reach it.

## What the monbus box still needs

The host has NO monbus-buffer readout: `MON_BASE`/`MON_LIMIT` are configured
by `run_characterization.py` and never read back, and no sequence decodes a
packet. Checking the monbus error packet is therefore its own piece of work
(a readout of the monitor window plus the shared `TBClasses.monbus` decoder),
not something to infer from a status bit. That box stays open deliberately.

## Verification record

| Run | Result |
|---|---|
| `val/amba` write-side injection cell, RED before the RTL | fails: `Parameters from the command line were not found in the design: ERR_INJECT` |
| `val/amba` write-side injection cell, after the RTL | pass; SLVERR lands on exactly the chosen burst |
| write-side mutation check (hold `fub_axi_bresp` at OKAY) | test FAILS, restore verified by `cmp` |
| `val/amba/test_axi4_slave_wr_crc_check.py`, whole file | 6/6 (the five ERR_INJECT=0 scenarios unchanged) |
| `val/amba` read-side injection cell, RED then GREEN | RED on the missing parameter, then pass |
| read-side mutation check (hold `fub_axi_rresp` at OKAY) | test FAILS on the SLVERR expectation only, restore verified |
| `val/amba/test_axi4_slave_rd_pattern_gen.py`, whole file | 6/6 |
| `val/amba/test_axi4_dma_slaves.py` (the wrapper) | 4/4 |
| verilator `--lint-only -Wall` elaboration, all three blocks | PINMISSING-clean after the fix below; the rest are pre-existing warnings in untouched files |
| yosys `-sv` parse, both harnesses + both slaves | 0 errors |

**One real bug the lint caught.** The first wrapper edit tied off only the
WRITE leaf; `u_rd_pattern_gen`'s five new inputs were left unconnected.
`test_axi4_dma_slaves.py` still passed 4/4, because Verilator defaults a
missing input pin to 0 and 0 is exactly "disarmed". A test cannot see that
class of mistake; only an elaboration warning can. (Related: the repo's lint
gate is a per-file yosys parse with no include path -- it cannot elaborate,
so it could not have caught this either.)

## A latent break found on the way

`make sim` / `make verify-sim` in BOTH Genesys 2 rapids areas sourced
`env_python` from a recipe with no `SHELL` set. `env_python` is bash
(`${VAR/x/y}`); `/bin/sh` is dash on this host, so every such recipe died with
`Bad substitution` and the pre-bitstream sim gate could not run at all. Fixed
with `SHELL := /bin/bash` in both Makefiles (the rapids DV Makefile already
had it). Unrelated to injection, but it blocks the gate this task has to pass.

## Board run (2026-10-01)

| Step | Result |
|---|---|
| bitstream, 8 ch / 256-bit / 4 KB per ch | WNS **+0.401 ns** at 100 MHz (0 of 263,899 endpoints failing), 78,426 LUTs (38.5 %), 68 BRAM; sha256 `754c3c2d...` |
| `verify-sim` gate inside the build | passed, 38.8 s (it runs at all only because of the `SHELL` fix recorded below) |
| program | startup status HIGH, identity verified |
| `BUILD` readback before measuring | 256-bit, 8 ch, 4 KB per ch, monitors/observers/gen_mon 0 -- the image built, not a stale one |
| `--byte-seq axi_resp_error --seq-level full` | **36/36 checks PASS**, 7,969 UART ops |

Two rounds x two halves, nine checks each, with a second channel running
alongside throughout: the slave issued the error (`ERR_STAT`, read at the
SLAVE), the sticky flag raised on the targeted channel ONLY, `CHANNEL_RESET`
cleared it, and both channels were golden against the byte-wise CRC after
recovery.

The timing margin is worth stating carefully: +0.401 ns against the +0.301 ns
of the previous byte build is NOT an improvement bought by this work. That
build had observers on (92,874 LUTs vs 78,426 here), so the two are different
designs and the delta is place-and-route variation. The honest claim is that
the injector cost no measurable margin.

## Still to do

- [ ] a monbus-buffer readout, then the error-packet check (see above) -- the
      last box in this task
