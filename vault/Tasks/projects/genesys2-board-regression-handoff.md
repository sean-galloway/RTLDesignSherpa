# Genesys 2 STREAM — board regression handoff (2026-08-25)

**The board is WORKING right now on the known-good image. Nothing is blocked.
The open problem: a freshly built bitstream regresses the board to zero beats
while every simulation passes.**

## Board state as you inherit it

- Programmed with `projects/fpga-systems/Genesys2/stream/stable/bitstream/
  stream_mon_8ch_allcones_obsmaster_obsslave.bit` (the last known-good image).
- Verified working after reprogramming: `1desc_1ch_1MB` = **65,583 cycles**,
  1524.8 MB/s, PASS -- bit-for-bit the historical baseline number.
- Genesys 2 UART is `/dev/ttyUSB0` (FT232R `AU05X8RM`). **`/dev/ttyUSB2` is a
  different board** (Digilent `210292BFA3EE`) -- pin the port explicitly.
- JTAG: pass `FPGA_JTAG_SERIAL=200300B818A0`. The script already resolves the
  `...A0` / `...A0B` ambiguity correctly (globs, then picks the target that has
  a device). Do not "fix" that.

## The problem

A bitstream built 2026-08-25 from the current tree programs and enumerates
correctly but moves **zero beats on every DMA config**, including
`1desc_1ch_1MB`, which passes on the old image with the identical host code.

Symptom detail from the failing image:

```
ch7 status  state=0x01  rd_beats=0x0  wr_beats=0x0
            flags=[desc_engine_idle, scheduler_idle, ch_enable,
                   rd_all_complete, wr_all_complete]
Aggregate over 0 cycles          <- perf window never opened
SCHED_ERROR = 0x00000000         <- no error raised
```

Channels enable, the descriptor engine never starts, nothing errors.

## ELIMINATED -- do not re-litigate these

Each was disproven by evidence, not argument. Several cost hours.

| candidate | how it died |
|---|---|
| Host Python broken | Old bitstream PASSES with the same unmodified host. `git log` confirms no register-writing `.py` was touched. |
| Current RTL broken | `test_stream_mon.py` passes 2/2 on the current tree. |
| `GEN_MON=0` (board) vs 1 (sim) | Ran the sim at `GEN_MON=0`: passes 2/2. |
| Descriptor-AXI monitor removal | See below; also covered by the `GEN_MON=0` run. |
| `DESC_MON_MAX_TRANS` sizing | 8ch x 8desc passes in sim WITH THE FIX REVERTED (52 min run). Theory dead. |
| Wrong bitstream / stale image | `CH0_CTRL_LOW` stores and reads back `0xDEADBEEF` -- only true post-kick-refactor. Board reports `nch=8 all-cones clk=90.0MHz`, `BUILD_CLK_HZ=0x055D4A80`. |
| Wrong synthesis generics | Makefile exports `STREAM_NUM_CHANNELS=8`, `MON_ERROR_FLAVOR=2`; the bitstream FILENAME encodes both (`8ch_allcones`). |
| Descriptors not reaching memory | `host_verify_descriptors.py`: **0/896 mismatches**. |
| Kick path wrong in host | `kick_channels` delegates to `batch_kick` = stage `CHx_CTRL_{LOW,HIGH}` then one `KICK_ENABLE`. Correct. |

## REMAINING candidates

1. **Timing marginality.** The failing build closed at **WNS +0.014 ns**; the
   working image is **+0.040 ns**. Both report 0 failing endpoints. Functional
   failure with clean timing reports is what marginal silicon looks like.
   *Cheapest discriminator:* rebuild at a slower clock (e.g. 85 MHz) changing
   nothing else. Works -> marginality. Fails identically -> structural.

2. **`SRAM_DEPTH` 256 (board) vs 512 (sim).** A real sim/board divergence, but
   **the owner has said to leave the buffer as is** -- do not change it. Noted
   only so the next session does not rediscover it as a "finding".

3. **A pending sim result.** At handoff time a Genesys cosim was running with
   row/col addressing default-on AND `GEN_MON=0` -- the closest sim has ever
   been to the board config. Check its outcome before anything else:
   `/tmp/claude-1000/-mnt-data-github-RTLDesignSherpa/*/tasks/bdpx18giu.output`
   (re-run via `/tmp/claude-1000/rowcol_sim.sh`). Passes -> points at (1).
   Fails -> the regression is reproducible in waveforms.

## The structural finding worth keeping

**No cosim elaborates `stream_genesys2_top`.** Every toplevel in the DV tree is
`stream_harness` (8 sites) or `dma_slave_monitors`. That is *correct* -- the top
is a thin 286-line board wrapper (MMCM, pins, LED, one `always`, three
`assign`s) -- so this is NOT a logic-coverage gap.

It is a **configuration**-coverage gap: the top overrides parameters the cosim
leaves at defaults, so sim and board build the same RTL at different settings.
Audited 2026-08-25:

| parameter | board | sim | status |
|---|---|---|---|
| `DATA_WIDTH` / `ADDR_WIDTH` | 128 / 32 | 128 / 32 | match |
| `AR/AW_MAX_OUTSTANDING` | 2 | 2 | match |
| `GEN_MON` | 0 | 1 | now overridable; tested, passes |
| `USE_ROW_COL_MAJOR_ADDRESSING` | 1 | was default 0 | FIXED -- now defaults 1 |
| `SRAM_DEPTH` | 256 | 512 | divergent BY DECISION -- leave |
| `DESC_RAM_ENTRIES` / `DEBUG_SRAM_WORDS` | 256 / 4096 | unset | still unaudited |
| `OBS_MAX_TRANSACTIONS` / `OBS_NUM_BANKS` / `OBS_USE_WDATA_ORDER_Q` | set | unset | still unaudited |
| `MON_N_PROFILE` | set | unset | still unaudited |

The bottom three rows are the remaining unexplored surface.

## Committed this session

| commit | what |
|---|---|
| `2dc11233` | bridge generator emits the depth params converters actually declare |
| `d8493de9` | `USE_DESC_AXI_MONITOR` default OFF (descriptor-AXI monitor opt-in) |
| `28ee1ccc` | `dma_8ch` coverage, `desc_perf` skip, `stable/` artifact slot |
| `1aa0b0d2` | `GEN_MON` env override so sim can reproduce the board |
| `db672cd0` | row/col-major addressing defaults ON in all 7 declarations |

### Descriptor monitor (`USE_DESC_AXI_MONITOR`)

Owner: *"only used to find the stream bug, no longer needed"*, default off, not
deleted. Gated via a dedicated parameter because `USE_AXI_MONITORS` kills ALL
monitors. Proven by differential elaboration: OFF removes 2 `axi_monitor_base`
cells + 1 `monitor_trans_cam`; the wrapper cell remains but is hollow.
Recovered 3,508 LUTs (68.20% -> 66.48%).

**Consequence:** `desc_perf` reads that monitor's perf window, so it is now a
structural zero. Skipped in lockstep with the parameter; `DESC_AXI_MON=1`
re-runs it. This gives up descriptor-bus perf coverage -- nothing else measures
it. `build-perf/host/host_desc_perf.py` is a standalone script that will read
zeros; it is called by no flow, Makefile or doc.

## Uncommitted -- belongs to ANOTHER agent, do not commit over it

- Bridge regeneration across four areas (components/bridge, Genesys2, both
  NexysA7 frameworks) after the converter refactor.
- `formal/converters/axi4_to_axil4_{rd,wr}/formal_axi4_to_axil4_{rd,wr}.sv` --
  hand-written harnesses that forwarded removed skid-depth params. Fixed here;
  both lint 0 errors. **No regen touches these** -- easy to miss, since the 53
  generated files fix themselves and these two silently do not.

## Landmines (each cost real time)

- **`make clean-all` in `build-mon` deletes the TRACKED `fpga/bitstream` and
  `fpga/reports`.** It happened FOUR times this session. It also destroyed the
  `.bit` that was on the board, so it can no longer be hash-compared against the
  build. `stable/` exists to survive this -- it is a sibling directory, outside
  the blast radius. **Rebuild -> hash the `.bit` -> program**, in that order.
- **Elaboration is not validation.** The failing bitstream was gated with
  `check_observer_params.sh`, which passed. That proves the design compiles and
  contains the right cones; it says nothing about whether data flows. The RTL
  had churned (converter refactor, bridge regen, APB4/APB5 fixes) since the last
  green sim, and the bitstream was built without re-running it. **Re-run the
  harness sim after ANY RTL churn, before building.**
- **The gate reads the reports directory, not the `.bit`.** After a `clean-all`
  it will happily quote the previous build's numbers. Check timestamps.
- **Do not assert a cause before demonstrating it.** Three theories were
  proposed and all three died. Reproduce first.

## Reproduction

```bash
# board, known-good (works today)
cd projects/fpga-systems/Genesys2/stream/build-perf
python3 host/host_characterize.py --port /dev/ttyUSB0 --configs 1desc_1ch_1MB

# sim at board config
/tmp/claude-1000/rowcol_sim.sh          # GEN_MON=0 + row/col, 8ch, monitors on

# rebuild (preserve the .bit BEFORE programming)
cd projects/fpga-systems/Genesys2/stream/build-mon
make clean-all && make bitstream
sha256sum fpga/bitstream/*.bit          # record it
NCH=8 FLAVOR=2 bash bin/check_observer_params.sh

# program
export FPGA_BITSTREAM=<abs path> FPGA_JTAG_SERIAL=200300B818A0
cd projects/fpga-systems/bin && vivado -mode batch -notrace -source program_fpga.tcl
```
