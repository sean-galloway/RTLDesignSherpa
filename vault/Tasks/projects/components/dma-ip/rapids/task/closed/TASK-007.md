# TASK-007: the MAS/HAS trees and index table describe the pre-wrapper SRAM architecture

**Priority:** P1. Readers are told the design has a per-channel unit array it does not have.
**Status:** CLOSED 2026-09-27 (see the closing note at the end); was open 2026-09-26. Found while doing the doc knock-on for `bdf4e0dff`.

**Ground truth.** `snk_sram_controller_beats.sv` and `src_sram_controller_beats.sv`
each instantiate STREAM's `sram_controller` **once**, at line 124, with
`genvar`/`generate` count **0**. There is no per-channel unit array any more, and
`snk_/src_sram_controller_unit_beats.sv` were deleted in `bdf4e0dff`.

**Seven files still assert the old shape.** This is structural, not naming:

| File | Claim |
|---|---|
| `rapids_beats_mas/rapids_beats_mas_index.md:125,127` | module-table rows for the deleted units, marked "Implemented" |
| `ch03_macro_blocks/README.md:45,50` | hierarchy tree shows `*_unit [8x]` |
| `ch03_macro_blocks/05_snk_sram_controller.md:39` | "Instantiates 8 `snk_sram_controller_unit` modules" |
| `ch03_macro_blocks/08_src_sram_controller.md:39` | same for `src_sram_controller_unit` |
| `ch01_overview/01_architecture.md:107,135,199,210` | data-flow steps + tree, with `beats_alloc_ctrl`/`simple_sram`/`beats_drain_ctrl` nested inside the unit |
| `rapids_beats_has/ch02_architecture/01_block_diagram.md:185,192` | HAS tree, `*_unit_beats [0..7]` |
| `ch02_fub_blocks/07_beats_latency_bridge.md:169` | `// In snk_sram_controller_unit` |

**Worse than the two unit rows.** ALL 23 filename cells in the index module table
use pre-`_beats` names and 16 of them resolve to no file: `scheduler.sv`,
`sink_data_path.sv`, `source_data_path.sv`, `beats_scheduler_group.sv`,
`snk_sram_controller.sv`, `descriptor_engine.sv`, `axi_read_engine.sv`,
`axi_write_engine.sv` and the rest -- every one marked "Implemented". Same fiction
as the `// Module:` headers ([[TASK-011]]).

**Why it was not folded into the rename commit (`d587852c2`).** The trees are
UTF-8 box-drawing art, so removing a nesting level means redrawing the `│`/`└`
connectors, not deleting a line. And correcting the index table is re-stating the
architecture, not repointing a path. Mixing that into a verified rename is how a
wrong tree ships inside a good commit.

**Done when:** no doc under `projects/components/dma-ip/rapids/docs/` names
`*_sram_controller_unit*` as live, every index-table filename resolves to a real
`.sv`, and the trees show `sram_controller` reached through the wrapper with
STREAM's `stream_alloc_ctrl`/`stream_drain_ctrl`/`stream_latency_bridge`.

**Related:** [[TASK-008]], [[TASK-009]], [[TASK-011]]. The rapids session owns the
RTL side and confirmed it is touching no `.md`.

---

**CLOSED 2026-09-27.** Index module table: every filename cell now names a real
`*_beats.sv` (or STREAM's `sram_controller.sv`), verified by resolving each
backticked `.sv` against `rtl/**` plus `../stream/rtl/**` -- 0 unresolved; the
two unit rows are gone and `rapids_src_beats`/`rapids_snk_beats` rows added.
Both MAS trees (`ch01_overview/01_architecture.md`, `ch03_macro_blocks/README.md`)
and the HAS tree (`ch02_architecture/01_block_diagram.md`) redrawn to the
instantiated hierarchy: core -> src/snk halves -> scheduler_group_array_beats +
data path -> `*_sram_controller_beats` naming wrapper -> STREAM `sram_controller`
-> `sram_controller_unit [0..7]` (stream_alloc_ctrl, gaxi_fifo_sync,
stream_drain_ctrl, stream_latency_bridge). ch01 data-flow steps and the
flow-control bullets say the same. `05_snk_sram_controller.md` and
`08_src_sram_controller.md`: overview, features, block figure and the
"Arbitration Logic" section (there is no round-robin arbiter inside; the consumer
selects with `drain_id`) rewritten. `grep -rn 'snk_sram_controller_unit|src_sram_controller_unit|_unit_beats|simple_sram' docs/` -> 0 live claims.
