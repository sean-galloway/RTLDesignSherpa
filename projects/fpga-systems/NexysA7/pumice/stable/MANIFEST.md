# Nexys A7 PUMICE (DDR2 characterization) — last stable build

**One slot. Overwrite it; do not accumulate versions.**

The RTL is NOT copied here. That is the whole reason this directory holds exactly
one build: a bitstream whose source you cannot reconstruct is only useful as
"the last thing known to work on the board." A second, older one is not useful at
all — you could not tell what differed, and you would not ship it. When a new
build supersedes this, replace every file here in one go and rewrite this
manifest.

This exists because `make clean-all` in `build-perf` deletes everything under
`fpga/bitstream` and `fpga/reports` — that is the correct behaviour for a build
directory, and it is why nothing worth keeping may live there. `stable/` is a
sibling of `build-perf`, outside that blast radius. Same convention as
`projects/fpga-systems/Genesys2/stream/stable/`; promote a build with
`make -C build-perf keep`.

## Contents

| path | what |
|---|---|
| ~~`bitstream/ddr2_char.bit`~~ | MOVED to HOLD, see below |
| `reports/` | Vivado timing / utilization / DRC / CDC / power for THIS bitstream |

## Measured (read from the reports in this directory, not retyped from memory)

```
WNS = +0.050 ns   TNS = 0.000   failing endpoints = 0 / 63160
WHS = +0.022 ns   THS = 0.000   failing endpoints = 0 / 63158
Slice LUTs = 20810 / 63400 = 32.82%
```

## Provenance

Moved here from `build-perf/fpga/` when the tracked-artifact problem was fixed
(the `fpga/` build dirs are now ignored). These files were previously tracked in
place, so their history is intact — `git log --follow` crosses the move.

The exact source tree that produced this bitstream is NOT pinned. Treat it as
"known-good on the board," not as reproducible from source. If reproducibility
matters for the next build, commit first and record the clean SHA here.

## What this build is known to do

DDR2 reads and writes are clean on the Nexys A7 (0/3072 beats in error) at the
bring-up tuple recorded in the DDR2 notes:

| | |
|---|---|
| `t_phy_wrlat` | 1 |
| `t_rddata_en` | 6 |
| `dfi_rddata_delay` | 7 |
| PHY bitslip / tap | 0 / 8 (eye width 17) |
| rate / burst | rate-2, BL4 |

## What it does NOT do — open

Residual row-sized corruption attributed to a refresh-collision arbiter bug. The
tiny-`tREFI` soak is the regression gate for that; it is not fixed here.

## Where the bitstream actually is

**NOT here.** Bitstreams are never committed (Sean, 2026-09-01): a multi-megabyte
binary whose source cannot be reconstructed from it costs git history forever,
never diffs, and goes stale silently against the RTL beside it.

    /mnt/data/fpga-hold/nexys_a7_100t/ddr2_char/ddr2_char.bit

`make keep` writes it there and leaves the reports here. `make program` uses the
build directory if a fresh build exists, and falls back to the HOLD copy
otherwise -- announcing which one it used, every time.

Override the location with `RDS_HOLD_DIR`. Keep one or two bitstreams in HOLD,
total: an older one you cannot tie to a source tree is not a backup, it is a
file you would never dare program.

The reports in this directory are the evidence for what that bitstream did, and
they stay in git precisely because they are text and they diff.
