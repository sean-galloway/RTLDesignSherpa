# STREAM 7–8 channel board timeout — handoff

**The kick refactor is DONE and validated. This is a separate, pre-existing-looking
regression found by the board perf sweep. Reproduce it in SIM first — the cosim has
no coverage of the failing corner.**

## The finding

Board perf characterization, 40 scenarios, union bitstream (8ch, all cones, 90 MHz):
**35 pass, 5 fail.**

| desc \ ch | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| 1 | P | P | P | P | P | P | P | P |
| 2 | P | P | P | P | P | P | P | P |
| 4 | P | P | P | P | P | P | P | **F** |
| 8 | P | P | P | P | P | P | **F** | **F** |
| 16 | P | P | P | P | P | P | **F** | **F** |

Failures are `timeout=True` with NO cycle count recorded. All five passed at
**100.00% utilization** in the baseline (`projects/NexysA7/stream_characterization/
reports/perf/matrix_2026-07-08_postfix.json`), completing in 64–128 ms.

**It is channel-driven, not size-driven** — `16desc_6ch` (96 MB) PASSES while
`8desc_8ch` (67 MB) FAILS. A clean staircase like that reads as contention scaling,
not a capacity limit.

### Already excluded

- **`SCHED_TIMEOUT_CYCLES`** — the host already programs `0xFFFFFFFF`
  (`characterization.py:393`). Not the scheduler write-timeout.
- **`AR_MAX_OUTSTANDING=2`** — would depress utilization *smoothly*, not produce
  binary timeouts, and 1–6ch are perfect. (It is still worth revisiting on its own
  merits: the comment at `stream_genesys2_top.sv:221` says "AR stays 2 for timing",
  a decision that predates the CAM banking and the 100→90 MHz move.)
- **The kick refactor** — 1–6ch match the baseline CYCLE-FOR-CYCLE
  (`1desc_1ch_1MB` = 65,583 cycles both runs).

### Prime suspect

Known repo failure class: 8-channel contention stranding the descriptor FIFO via a
sticky `CH_ERROR`. See `[[project_stream_desceng_prefetch_and_sched_timeout]]` —
the earlier instance was fixed by wiring `cfg_prefetch_enable`/`fifo_threshold` and
sizing the scheduler timeout to the workload. Check whether the board path programs
prefetch the way the sim path does.

## START HERE — reproduce in sim, the cosim does NOT cover this

`SIM_NUM_CHANNELS=8` only sets how many channels are BUILT. The tests drive at most
**4 active channels × 4 descriptors**:

| case | ch × desc |
|---|---|
| `obs_equiv` | 4 × 4 (`cocotb_stream_harness.py:320`) |
| `test_stream_mon` | 1 × 4 |
| others | 1 × 1 |

The failing corner (7–8ch × 8–16desc) is never simulated. The knobs already exist —
`num_ch`, `desc_per_ch`, `xfer_bytes` at `cocotb_stream_harness.py:135-137`, driven
from env, plus `DMA_TIMEOUT_CLOCKS` (default 50000, will need raising). So this is a
matter of driving them, not new infrastructure.

Sim gives what the board cannot: waveforms on the descriptor FIFO and scheduler
state at the moment it strands.

## Reproduce

```bash
cd projects/fpga-systems/Genesys2/stream/build-mon
make clean-all                     # ALWAYS
cd dv/tests
SIM_NUM_CHANNELS=8 DMA_TIMEOUT_CLOCKS=2000000 \
  python3 -m pytest test_stream_mon_perf.py -k rw_perf -q
# then drive num_ch=8, desc_per_ch=8 through the harness env
```

Board re-run (bitstream already programmed and committed):

```bash
cd projects/fpga-systems/Genesys2/stream/build-perf
python3 host/host_characterize.py --port /dev/ttyUSB0 --output results.csv
# NOTE: --output writes CSV regardless of a .json extension
```

## What IS validated (do not re-litigate)

- STREAM FULL sign-off: **800 tests** (fub 121, macro 635, top 44).
- Genesys 2 cosim @ 8ch: monitor **2/2**, perf **3/3**;
  `OBSERVER EQUIVALENCE PASSED`, in-core 4096/4096 == observer 4096/4096.
- Board: `build v1 all-cones nch=8 clk=90.0MHz`, `KICK_ENABLE` live @ 0x128,
  `comp_sram` read/write verified, WNS **+0.040 ns**, 0 failing endpoints,
  **68.20%** LUTs.
- 35/40 board scenarios match the baseline exactly.

## Landmines (each cost real time)

- **`make clean-all` before EVERY build/run.** And in `build-mon` it ALSO wipes the
  tracked `fpga/bitstream` + `fpga/reports` — that is how a verified bitstream got
  deleted mid-session and the deletion committed. Rebuild before staging artifacts.
- **Sweep for ALL symbols, not one call site.** The UART TB had FOUR kick sites;
  checking one and generalizing missed three.
- **Baseline before blaming.** Three times this session "surely pre-existing" was
  wrong (and once, right). `git stash` + rerun settles it in minutes.
- **Never verify build content from `get_cells -hier` or timing-path greps** — use
  `build-mon/bin/check_observer_params.sh` (Verilator elaboration).
- **A bridge slave in the TOML but missing from the connectivity CSV** silently
  generates a portless slot and exits 0. Tell: `Total: N slaves` vs
  `Connectivity matrix: N-1 slaves`.
- `export A=$B` in the SAME statement that defines `B` expands empty — bit me twice.

## Also fixed here

`characterization.py` now reads **`BUILD_CLK_HZ` from the board** instead of
assuming 100 MHz; `--aclk-mhz` is demoted to an override. The old constant was
correct on the Nexys A7 and 11% wrong on this 90 MHz board, silently scaling every
MB/s figure. Baseline MB/s numbers remain valid — that board really was at 100 MHz.
