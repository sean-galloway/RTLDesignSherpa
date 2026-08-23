# STREAM kick refactor — validation handoff

**State: RTL complete and lint-clean (0 errors). NOTHING COMMITTED. Not simulated, not built, not run on the board.**

## What changed and why

The kick path had two mechanisms and neither stored the descriptor address:

- `apb4todescr` snooped the **raw APB command stream**, decoding `0x000-0x03F` itself, so
  the *address write itself* kicked. The address existed nowhere as readable state, and an
  8-channel launch cost 8 APB-over-UART writes — channel 0 had been running for
  milliseconds before channel 7 started, biasing every cross-channel perf window.
- `i_kick_burst_*` top-level ports existed **only** to work around that latency, driven from
  `harness_csr`.

Both are replaced by: stage 8 x 64-bit addresses, then launch with ONE write.

| | |
|---|---|
| `CH{n}_CTRL_LOW/HIGH` @ `0x000-0x03F` | now **stored** (`sw=rw; hw=r`), exported via `hwif_out` |
| `KICK_ENABLE` @ **`0x128`** | 8 x 1-bit `singlepulse` (`KICK0..KICK7`) |
| `cmdrsp_router` | `addr_hit_m0 = 1'b0`; `0x000-0x03F` now falls through to the regblock on the default m1 route |
| `stream_top_ch8` | one kick source (`hwif_out` + pulse -> pending latch -> `apb_valid/apb_addr`); `apb4todescr` instance and `i_kick_burst_*` ports removed; retired router m0 tied to safe constants |
| `stream_harness` | `kick_burst` connections removed |

### Two constraints that forced design choices

1. **`KICK_ENABLE` is at `0x128`, not `0x040`.** `0x040-0x0FF` is the perf profiler's window
   in `cmdrsp_router` (`0x040` = `PERF_CONFIG`), and `0x000-0x03F` is exactly full at
   8 x 64-bit. It therefore sits with the other per-channel controls next to
   `CHANNEL_ENABLE`/`CHANNEL_RESET`.
2. **Eight 1-bit fields, not one 8-bit field.** SystemRDL requires `singlepulse` width 1.
   They share one register, so a single 32-bit write still launches every channel on the
   same cycle — atomicity is a property of the bus transaction, not the field width.

## THE VALIDATION SURFACE — read this first

**~30 host/TB call sites still write `CH{n}_CTRL_*` expecting the write to kick.** They will
now stage an address and **silently never launch**. This is the dominant risk: tests will not
error, they will hang or report zero work. Every caller must add a `KICK_ENABLE` write.

Known call sites (`grep -rn "CH[0-9]_CTRL_"`):
- `projects/components/dmas/stream/dv/tbclasses/stream_core_tb.py` (7)
- `projects/fpga-systems/Genesys2/stream/build-perf/dv/tests/test_stream_device.py` (6)
- `projects/fpga-systems/Genesys2/stream/bin/stream_device.py` (3)
- `projects/fpga-systems/Genesys2/stream/build-perf/dv/tests/test_stream_ext_suite.py` (2)
- NexysA7 `flows-stream-bridge` mirrors (reference-only per owner; needs no build)

## Suggested order

1. Update `stream_device.py` + `stream_core_tb.py` to stage-then-kick. This is the API change.
2. `make clean-all` then STREAM cosim (`dv/tests`, fub/macro/top) — catches the silent no-launch.
3. Genesys2 UART cosim: `build-mon/dv/tests` perf (3) + monitor (2), `SIM_NUM_CHANNELS=8`.
4. `make clean-all && make bitstream` in `build-mon`, gate with
   `bin/check_observer_params.sh`, program, re-run the board checks.
5. Only then consider deleting `rtl/fub/apb4todescr.sv` + its `.f` + its test. **Currently
   only unhooked, deliberately** — the module and its test still exist.

## Landmines (learned the hard way this session)

- **`make clean-all` before EVERY build/run**, sim included. Two debug iterations returned
  byte-identical stale output and sent the investigation after an imaginary bug.
- **A `clean-all` in `build-mon` also wipes `fpga/bitstream` + `fpga/reports`** (tracked
  files). It deleted a verified bitstream mid-session. Rebuild before committing artifacts.
- **Never verify build content from Vivado `get_cells -hier` or timing-path greps.** Timing
  reports list only reported paths (CAM bank 2 has *never* appeared in any report), and
  synthesis inlines purely combinational blocks so `g_err`/`g_to`/`g_compl` are invisible.
  Use `bin/check_observer_params.sh`, which elaborates via Verilator `--xml-only`.
- **Regenerate regs only via `bin/peakrdl_generate.py`**, and pass
  `--regmap-output projects/components/dmas/stream/rtl/stream_regmap.py` — the RTL is
  consumed from `regs/generated/rtl/` but DV/host read `rtl/stream_regmap.py`. Two paths,
  one invocation, or they drift.

## Board / environment

- Genesys 2 attached: JTAG `200300B818A0` (use target `...A0B`, the bare `...A0` has no chain);
  UART is a separate FT232R `AU05X8RM` on `/dev/ttyUSB0`.
- Program with `projects/fpga-systems/bin/program_fpga.tcl` (`FPGA_BITSTREAM=`, `FPGA_JTAG_SERIAL=`).
- Board currently holds the **pre-refactor** union bitstream (8ch, all cones, 90 MHz,
  `BUILD_CLK_HZ=90000000`). It does NOT contain this refactor.

## Uncommitted (hand-edited)

```
stream: rtl/macro/stream_regs.rdl, rtl/stream_regmap.py, rtl/top/cmdrsp_router.sv,
        rtl/top/stream_top_ch8.sv, rtl/filelists/top/stream_top_ch8.f
genesys2: rtl/stream_harness.sv, rtl/harness_csr.sv, rtl/harness_csr_regmap.py,
          bin/harness_addrs.py, bin/gen_harness_regmap.py     <- BUILD_CLK_HZ work
          build-mon/fpga/{bitstream,reports}                  <- pre-refactor artifact
```
Plus regenerated `regs/generated/**`. `bin/review/REVIEWER_BRIEF.md` is ANOTHER session's — leave it.

The `BUILD_CLK_HZ` work (separate from the kick refactor) is finished and verified on
hardware: `0x101DC = 90000000`, `describe_build` reports `clk=90.0MHz`. It is commit-ready.
