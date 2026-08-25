# Genesys 2 STREAM — last stable build

**One slot. Overwrite it; do not accumulate versions.**

The RTL is NOT copied here. That is the whole reason this directory holds exactly
one build: a bitstream whose source you cannot reconstruct is only useful as
"the last thing known to work on the board." A second, older one is not useful at
all — you could not tell what differed, and you would not ship it. When a new
build supersedes this, replace every file here in one go and rewrite this manifest.

This exists because `make clean-all` in `build-mon` deletes tracked files under
`fpga/bitstream` and `fpga/reports`. That has destroyed a verified bitstream more
than once. `stable/` is a sibling of `build-mon`, outside that blast radius.

## Contents

| path | what |
|---|---|
| `bitstream/stream_mon_8ch_allcones_obsmaster_obsslave.bit` | the programmed artifact |
| `reports/` | Vivado timing / utilization / DRC / CDC / power for THIS bitstream |
| `results/` | board perf sweeps (7 CSVs) measured on THIS bitstream |

## Build configuration

| | |
|---|---|
| channels | 8 (`NUM_CHANNELS=8`) |
| monitor cones | `MON_ERROR_FLAVOR=2` — union (all cones, incl. error) |
| observers | master + slave interface observers |
| clock | 90.0 MHz (VCO 1350 / CLKOUT0_DIVIDE 15), period 11.111 ns |
| `BUILD_CLK_HZ` | `0x101DC = 90000000`, read back from the board |
| kick | `KICK_ENABLE` @ `0x128` (stage `CHn_CTRL_LOW`, then one write) |
| CAM banks | 4 (64 transactions / 4 banks) |
| `AR_MAX_OUTSTANDING` | 2 |

## Measured (gates passed before these were quoted)

```
WNS = +0.040 ns   TNS = 0.000   failing endpoints = 0   WHS = +0.044 ns
Slice LUTs = 138996 / 203800 = 68.20%
```

Content verified by `build-mon/bin/check_observer_params.sh` (Verilator
`--xml-only` elaboration): 4 CAM banks, error cone present, 11.111 ns in the
timing summary. Do NOT re-verify build content with Vivado `get_cells -hier` or
by grepping timing paths — both have produced false conclusions here.

## What this build is known to do

- Serves BOTH the perf and the monitor flow from one bitstream (deliberate).
- 35 of 40 board perf scenarios match the pre-existing baseline.
- `comp_sram` read/write verified on the board.

## What it does NOT do — open

Five board perf scenarios time out, all at high channel count:

`4desc_8ch_1MB`, `8desc_7ch_1MB`, `8desc_8ch_1MB`, `16desc_7ch_1MB`, `16desc_8ch_1MB`

Root cause is UNKNOWN. A `DESC_MON_MAX_TRANS` sizing theory (descriptor-fetch
monitor table flat at 16 while shared by all channels) was tested and **did not
reproduce in sim**: 8ch x 8desc x 8KB passes with the fix reverted. The sim
workload is 128x smaller than the failing board scenario (8 KB vs 1 MB per
descriptor), so the negative result bounds the theory rather than killing it —
but the theory is unproven and nothing here should be described as fixed.

## Source state

Captured at `a7244fb2` (branch `main`), working tree dirty at the time. The exact
tree that produced this bitstream is NOT pinned — recording a SHA against a dirty
tree would be a false provenance claim. Treat this artifact as "known-good on the
board," not as reproducible from source. If reproducibility matters for the next
build, commit first and record the clean SHA here.
