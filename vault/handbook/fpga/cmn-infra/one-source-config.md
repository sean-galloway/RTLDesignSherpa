---
title: One source for build config
summary: Board and sim elaborate from ONE package. A restated literal is how they drift, silently and green.
---

# One source for build config

A harness parameter must have exactly one home, and both the board top and
every cosim must read it from there. Restating a value "to be explicit" is not
documentation - it is a second owner, and second owners drift.

The drift is silent by construction. A config divergence does not fail a test;
it changes what the test *means*. Every run stays green while measuring
something the board will never build.

## What it cost (STREAM Genesys 2, measured 2026-08-25)

`stream_char_cfg_pkg` existed but carried four parameters, of which the board
top read two. Everything else was hand-written in three more places - the board
top, build-mon's cosim, build-perf's cosim - and all three disagreed, with each
other and with the package:

| param | board | build-mon | build-perf | pkg |
|---|---|---|---|---|
| `AR/AW_MAX_OUTSTANDING` | 2 | 2 | **16** | 8 (read by nobody) |
| `RESP_DELAY_R_CAPACITY` | 256 | 512 | 512 | 256 |
| `RESP_DELAY_B_CAPACITY` | 16 | 512 | 32 | 16 |
| `SRAM_DEPTH` | 256 | 512 | 512 | absent |
| `DESC_RAM_ENTRIES` | 256 | 2048 | 128 | absent |
| `DEBUG_SRAM_WORDS` | 4096 | 65536 | 4096 | absent |

build-perf was characterizing an engine with **8x the outstanding depth the
board builds**, so its throughput numbers were never capable of predicting
silicon. The 2048/65536 entries were harness defaults nobody passed - a
"big ASIC target" no build ever used - so a cosim that simply omitted a
parameter got 8x the descriptor RAM and 16x the trace depth of the board
without a line of code saying so.

Second-order damage: because the unpassed parameters silently fell to those
defaults, **no cosim had ever elaborated the board's configuration**, so a
month of "sim passes, board fails" comparisons were not comparisons at all.

## The rule

- Geometry lives in the cfg package. The RTL parameter DEFAULTS reference it
  (`parameter int SRAM_DEPTH = stream_char_cfg_pkg::CFG_SRAM_DEPTH`), so any
  elaboration that stays quiet inherits silicon's value.
- The board top passes per-BUILD flavor and Vivado generics ONLY. If it names a
  geometry literal, that is the bug.
- A cosim lists deviations, never restatements, and each deviation carries its
  reason at the call site.
- Python reads the package rather than mirroring it - parse the `.sv`
  (`Genesys2/stream/dv/stream_cfg.py`) so a moved value moves everywhere.
- Keep an A/B override path (`SIM_*` env vars). The package is what the NEXT
  bitstream uses; reproducing a part already on the bench means pinning what it
  was built at, which is not the same thing.
- Guard it. `build-mon/dv/tests/test_stream_cfg_single_source.py` fails if a
  literal returns, and is mutation-checked - a guard nobody has seen fail is
  not known to work.

## Traps

- **A parameter can be coherent only as a set.** Outstanding depth, R capacity
  and SRAM depth move together (`R >= outstanding x max_burst`,
  `depth = outstanding x burst x 2`). Raising one alone lets the modeled memory
  back-pressure and mask the very throughput being measured. The guard asserts
  these relations, not just the values.
- **Tool limits masquerade as design decisions.** AR/AW had settled at 2
  everywhere with comments justifying it on monitor-CAM timing. The real
  binding constraint in sim was Verilator: at AR/AW=8 with monitors on,
  `unroll-count 4096` leaves 6 BLKLOOPINIT errors and 16384/200000 compiles
  clean. A workaround that acquires a rationale is worse than one that stays
  ugly - it stops looking like a workaround.

Transport has the identical failure one layer up: see [[uart-harness]].
Layer map: [[host-stack]].
