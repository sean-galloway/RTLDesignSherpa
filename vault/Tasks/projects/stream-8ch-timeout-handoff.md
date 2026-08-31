# STREAM 7-8 channel board timeout — handoff

> **UPDATE 2026-08-31: does NOT reproduce on the dedicated perf build.**
> A `build-perf` bitstream (USE_AXI_MONITORS=0, 8ch, 100 MHz, WNS +1.582 ns,
> sha256 c49a1b76...) sweeps **40 of 40 scenarios PASS**, all five former
> failures included, at full rate:
>
> | scenario | data | cycles | MB/s |
> |---|---|---|---|
> | 4desc_8ch_1MB | 32 MB | 2,097,199 | 1525.8 |
> | 8desc_7ch_1MB | 56 MB | 3,670,063 | 1525.9 |
> | 8desc_8ch_1MB | 64 MB | 4,194,351 | 1525.9 |
> | 16desc_7ch_1MB | 112 MB | 7,340,079 | 1525.9 |
> | 16desc_8ch_1MB | 128 MB | 8,388,655 | 1525.9 |
>
> Whole sweep in 2m49s, throughput flat at 1524.8-1525.9 MB/s across every
> channel count 1-8. Raw log: `build-perf/results/perf_sweep_2026-08-31.txt`.
>
> **This is NOT a like-for-like retest and must not be read as "fixed".** The
> failures above were measured on the union MONITOR bitstream (all cones,
> 90 MHz); this is the monitors-off perf build at 100 MHz. Two variables moved
> at once, plus a week of tree churn. What it does do is put weight behind the
> one theory this page could not kill: the failure is monitor-side, not
> datapath-side. The descriptor-fetch monitor's transaction table is flat at 16
> and SHARED by every channel, which is the only structure here that scales with
> channel count -- and the staircase below (16desc_6ch passes at 96 MB while
> 8desc_8ch fails at 67 MB) is contention-shaped, not capacity-shaped.
>
> To actually settle it, rerun the sweep on a monitor bitstream from today's
> tree. If the five fail there and pass here, the monitors are the difference
> and DESC_MON_MAX_TRANS is the next thing to size. If they pass there too, the
> cause was something that landed in the tree since 2026-08-25 and this page is
> closable.
>
> **ATTEMPTED 2026-08-31, BLOCKED: build-mon does not close timing.** Built from
> ef17c6ad+ (8ch, all cones, 90 MHz, clean-all, 45 min):
>
>     WNS -1.733 ns   TNS -9241.753   7597 failing endpoints of 326977
>     vs stable Aug-24: WNS +0.040, 0 failing of 263545
>
> 7182 of the 7597 failing destinations are inside `trans_mgr`'s banked CAM;
> worst path is CROSS-BANK, `g_cam_bank[1]` -> `g_cam_bank[2]`, 12.299 ns against
> an 11.111 ns requirement and 67.5% of that is ROUTE. Congestion, not deep logic.
> Fewer LUTs than stable (126628 vs 138996) but 24% more endpoints.
>
> Not programmed. A design missing setup by 1.7 ns produces arbitrary behaviour,
> so a sweep on it would yield numbers that mean nothing -- which is exactly the
> trap this page already fell into once.
>
> NOT the bank count (7b4cabca, 4 -> 8): stream_cfg_pkg.sv records 4 banks
> measuring -4.150 ns with the same hotspots, so 8 was already a mitigation.
> The likelier driver is AR/AW_MAX_OUTSTANDING 2 -> 8 -- stable closed with a
> 24-slot table, the package now asks for 72. Reported to the monitor owner.
>
> **So the like-for-like retest is still owed**, and it now needs one of:
> (a) build-mon timing fixed, or (b) build-mon rebuilt at a clock where it
> closes (-1.733 ns at 11.111 ns implies about 78 MHz). Option (b) still
> isolates monitors-vs-not at a VALID operating point, which is what the
> question needs -- the timeout is a functional failure, not a frequency one.


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

## TREAT THIS AS A STREAM RTL BUG, NOT A HOST TIMEOUT

Owner's guidance (2026-08-24): **the last time this symptom appeared it was a real
bug in STREAM.** Do not start from "the host poll timed out" -- start from "what in
STREAM strands under high channel contention".

The prior instance ([[project_stream_desceng_prefetch_and_sched_timeout]]) was a
1000-cycle scheduler write-timeout firing under 8-channel contention, setting a
sticky `CH_ERROR` that stranded the descriptor FIFO. It never reproduced at macro
level because the timeout was a settable INPUT there but register-driven at top --
so a TB signal poke was dead code and only the top-level path could show it. Expect
the same asymmetry here: reproduce at the level that owns the register.

Both halves of that fix are still in place, so this is a NEW instance of the class,
not a regression of it:
  * `cfg_prefetch_enable` / `cfg_fifo_threshold` are wired in
    `descriptor_engine.sv` (lines 124-125, 240, 466).
  * `characterization.py:393` programs `SCHED_TIMEOUT_CYCLES = 0xFFFFFFFF`.

So look for what ELSE strands at 7-8 channels. Useful first reads on a hung board,
before resetting it: `SCHED_ERROR`, `CHANNEL_IDLE`, `DESC_ENGINE_IDLE`,
`SCHEDULER_IDLE`, and the per-channel `CH_STATE{0..7}_STATE` -- a stranded channel
should show which stage it died in. `host_status.py` dumps most of these.

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
