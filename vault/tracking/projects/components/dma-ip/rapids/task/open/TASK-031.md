# TASK-031: Strap values on RAPIDS and the Hive strap contract

**Priority:** P3
**Status:** open -- 2026-10-19, split from rapids TASK-027
**Owner:** sean galloway

## Why

rapids TASK-027 built the straps toward RAPIDS (TILE_SPEC 11.9-11.11) as
top-level parameters with defaults. TILE_SPEC 11.9 makes the straps a
Hive-level contract: the Hive sets every strap and checks that the cells,
the control cores and RAPIDS agree. Nothing yet records which values RAPIDS
uses, how the Hive learns them, or that the spec's status section still
says the straps are not built.

## Working values (best guess 2026-10-19; owner: they probably won't change)

The RAPIDS straps are fixed at build time, not run-time CSRs:

| Strap | Parameter | Value | Why this value |
|---|---|---|---|
| Landing space per cell | `TILE_LAND_FLITS` | 16 flits, header included | TILE_SPEC 11.9 default; a cell packet to RAPIDS is at most 16 flits (1 header + 15 data beats) |
| Intake entries per control core | `TILE_DESC_PER_CORE` | 2 | Matches the two-deep descriptor skid in every scheduler (rapids TASK-028) |
| Intake queue depth | derived | 4 cores x 2 = 8 | `rapids_pkg::TILE_NUM_CORES` x `TILE_DESC_PER_CORE` |
| Total landing space | derived | 16 cells x 16 = 256 flits | `rapids_pkg::TILE_NUM_CELLS` x `TILE_LAND_FLITS` |
| Sink SRAM per channel | `SRAM_DEPTH` | >= `TILE_LAND_FLITS` + 4 = 20 (default 4096) | `rapids_snk` `$fatal` check: a whole packet drains only when the channel has that much room |
| Resync `set` values | same parameters | 16 (class 0), 2 (class 1) | `rapids_tile_credit_tx` sends the build-time straps |

The same values apply to every RAPIDS top that has the tile header
(`rapids_top`, `rapids_cxs_top`, the 8ch and 16ch tops). The RAPIDS Beats
tree has no tile header (`TILE_HDR` / `TILE_CREDITS` exist only in the byte
tree), so it has no straps; if it ever gains the tile header it takes the
same values.

## What to do

1. **Report the straps in a CSR.** A read-only `TILE_STRAPS` register
   (`LAND_FLITS`, `DESC_PER_CORE`, driven from the parameters) so the Hive and
   test software read RAPIDS's straps instead of assuming the defaults. Regen
   both RDLs, the regmaps and the tops; a test reads it by name and checks it
   against the build parameters, including a non-default build.
   **Placement (owner 2026-10-19):** at the very top or bottom of the config
   space, not counting the monitor block. Each half's regfile is config
   0x000-0x7FF with `MON` at 0x800 (8ch and 16ch alike). The bottom, 0x000,
   is `CH0_DESC_ADDR_LOW`, so it goes at the top: **0x7FC** (last used offset
   today is `HIST_TOTAL` 0x380), i.e. `SRC.TILE_STRAPS` at 0x07FC. The
   regfile is shared, so `SNK.TILE_STRAPS` (0x17FC) reads the same values.
2. **TILE_SPEC 11.12** (RAPIDS implementation status): replace "straps not
   built" with what TASK-027 built and these values, and note the
   deviations: resync sends one `set` per sender rather than a multicast;
   the stall checks are RAPIDS-local, not a shared ocelus module; read
   replies into RAPIDS are not strap-accounted; only cells hold landing
   space. That file had another session's uncommitted edits on 2026-10-19;
   edit it once they are committed.
3. **Hive side (record, not build here):** the cells' strap counters start
   at `TILE_LAND_FLITS` and the cores' at `TILE_DESC_PER_CORE`, set from
   the same Hive parameters. RAPIDS adds no cross-check (owner ruling
   2026-10-18); the CSR in item 1 is what the Hive checks.

## Done when

- `SRC.TILE_STRAPS` (0x7FC) reads back the build parameters in a default and a
  non-default build; the MAS 3.14 and HAS register text name it.
- TILE_SPEC 11.12 states the built straps and their values.
- RAPIDS byte regression clean-all FULL.
