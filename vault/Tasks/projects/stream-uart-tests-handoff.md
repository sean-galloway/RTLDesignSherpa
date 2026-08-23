# STREAM UART tests — handoff (update the cosim for the internalized kick)

**Task: update the Genesys 2 UART cosim tests. Nothing in this change set is committed.**

## START HERE — the cosim is currently broken at import

```
$ python3 -c "import stream_harness_tb"
KeyError: "unknown HARNESS register 'KICK_GO'"
```

`dv/tbclasses/stream_harness_tb.py:95` does `CSR_KICK_GO = H("KICK_GO")` at MODULE
SCOPE. `KICK_GO` was removed from the harness CSR (see below), so the import raises
and **both** UART tests fail before running:

- `build-mon/dv/tests/test_stream_mon.py` (monitor mode, 2 tests)
- `build-mon/dv/tests/test_stream_mon_perf.py` (perf mode: desc_perf, rw_perf, obs_equiv)

Failing loudly at import is the intended outcome of by-name register access — it is
not a mystery, just unfinished work.

### What to change in `stream_harness_tb.py`

| line | now | should be |
|---|---|---|
| 95 | `CSR_KICK_GO = H("KICK_GO")` | delete |
| 109-114 | `kick_addr_csr()` -> `H(f"CH{ch}_KICK_ADDR")` | `A(f"CH{ch}_CTRL_LOW")` (a STREAM reg now) |
| 134-135 | `APB_CH_KICK_BASE` "kick-off via apbtodescr" | comment is stale; writes no longer kick |

The working reference implementation is already written — copy its shape:
`bin/harness_kick.py::batch_kick()` stages `CHx_CTRL_{LOW,HIGH}` then writes
`KICK_ENABLE` once. `bin/stream_device.py` has `kick()` and `kick_many()`.

## Why the kick changed

`CHx_CTRL_{LOW,HIGH}` (0x000-0x03F) used to be write-only address-map placeholders
with NO storage; `apb4todescr` snooped the raw APB command stream so the WRITE
ITSELF kicked. Two consequences: the descriptor address was never readable state,
and an 8-channel launch cost 8 APB-over-UART writes — channels started milliseconds
apart, biasing every cross-channel measurement.

Now: addresses are ordinary stored registers, launch is one write to
**`KICK_ENABLE` @ 0x128** (eight 1-bit `singlepulse` fields KICK0..KICK7). One
32-bit write starts every channel on the same clock edge.

**0x128, not 0x040**, because 0x040-0x0FF is the perf profiler window in
`cmdrsp_router` and 0x000-0x03F is exactly full at 8 x 64-bit.

### The bug this already caused — do not re-introduce it

`peakrdl_to_cmdrsp` holds `regblk_req` across CMD_IDLE -> CMD_WAIT_ACK (deliberate;
the one-cycle variant broke every register read and was reverted). A PeakRDL
`singlepulse` fires once per decoded write strobe, so a held request pulses KICKn
**twice** and the channel launches twice — exactly 2x the descriptor's beats.
Fixed by rising-edge detect in `stream_top_ch8`:
`w_kick_edge = w_kick_pulse & ~r_kick_pulse_d`. A `singlepulse` field is only
single-pulse if the adapter's request is single-cycle; nothing in the RDL says so.

## State of everything else (all lint-clean, 0 errors)

**Simulation is green at FULL sign-off**: fub 121, macro 635 (+3 skipped),
top 44 (+1 xfailed) = **800 passed**, `run-all-full-parallel` OK in every area.

| area | state |
|---|---|
| RTL kick path | done; `apb4todescr` + `i_kick_burst_*` unhooked from STREAM |
| STREAM TB | `kick_off_channel()` launches; `kick_off_channels_together()` added |
| Genesys host | `stream_device`, `harness_kick`, `characterization`, `stream_ext_suite`, `stream_ext_report` all repointed at KICK_ENABLE |
| `harness_csr` | KICK_GO/CH_KICK_ADDR removed (803->746 lines); regmap regenerated, 75 regs |
| `BUILD_CLK_HZ` | done AND verified on hardware: `0x101DC = 90000000`, `clk=90.0MHz` |
| `comp_sram` | bridge slave @ 0x001A0000 (64 KB) + `sdpram_slave_axil_axil` wired in harness |
| `apb4todescr` | STILL EXISTS — **RAPIDS instantiates it twice** (`u_kick_src`, `u_kick_snk`). Do not delete. STREAM's MAS docs for it were removed; RTL/tests/formal stay. |

## After the cosim imports again

1. `make clean-all` (ALWAYS — see landmines) then run both UART suites at
   `SIM_NUM_CHANNELS=8` to match the bitstream. Perf takes ~80 min; use
   `OBS_EQUIV_SCALE=16` to shrink obs_equiv transfer size ONLY.
2. Consider a cosim check for `comp_sram`: write the window, read it back. It is
   wired but has never been exercised.
3. Board: `make clean-all && make bitstream`, gate with
   `build-mon/bin/check_observer_params.sh`, program via
   `projects/fpga-systems/bin/program_fpga.tcl`, re-run the host checks.

## Landmines (each cost real time this session)

- **`make clean-all` before EVERY build/run, sim included.** Two debug iterations
  returned byte-identical stale output and sent the investigation after an
  imaginary bug.
- **`clean-all` in `build-mon` also wipes tracked `fpga/bitstream` + `fpga/reports`.**
  It destroyed a verified bitstream mid-session; rebuild before committing artifacts.
- **Never verify build content from Vivado `get_cells -hier` or timing-path greps.**
  Timing reports list only reported paths (CAM bank 2 has never appeared in any) and
  synthesis inlines combinational blocks, so the error/timeout/compl cones are
  invisible. Use `check_observer_params.sh` (Verilator `--xml-only` elaboration).
- **A bridge slave in the TOML but missing from the connectivity CSV generates a
  PORTLESS slot and exits 0.** Only tell: `Total: 13 slaves` vs
  `Connectivity matrix: 12 slaves` in the regen log.
- **Baseline before blaming.** Twice this session "surely pre-existing" was wrong;
  `git stash` + rerun took minutes and changed the answer both times.
- Regenerate regs only via `bin/peakrdl_generate.py`, passing
  `--regmap-output .../rtl/stream_regmap.py` (RTL is consumed from
  `regs/generated/rtl/` but DV/host read `rtl/stream_regmap.py`).

## Board / environment

Genesys 2 attached. JTAG `200300B818A0` — use target `...A0B`, the bare `...A0` has
no chain. UART is a separate FT232R `AU05X8RM` on `/dev/ttyUSB0`. The board
currently holds a **pre-kick-refactor** bitstream (8ch, all cones, 90 MHz).

## Also filed

`vault/Tasks/projects/components/dmas/stream/open.md` — tally decompression
(LOW priority; `comp_sram` unblocks compression testing without it).
