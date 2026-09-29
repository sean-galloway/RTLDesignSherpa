# ISSUE-001: 74 doc instantiation examples name modules with no .sv -- generated, planned, or fabricated?

**Priority:** P2. Unknown split between harmless and real.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-09-26. Raised as an ISSUE, not a bug, because the
classification is genuinely undetermined.

**Measured** repo-wide: 78 instantiations inside ```systemverilog fences name a
module with no matching `.sv`. 4 are rapids and deliberately held
([[rapids TASK-009]]); the other 74 are unclassified:

| Area | Ghosts |
|---|---|
| `docs/markdown` (RTL library book) | 31 |
| `projects/components/fabric-gen-ip/bridge/docs` | 12 |
| `projects/components/delta` | 9 |
| `projects/components/converters/docs` | 5 |
| `projects/components/dma-ip/stream` | 4 |
| `projects/components/hive/PRD.md` | 3 |
| apbx-xbar, misc, RLB, user-guides | 10 |

**Three different things are mixed in here, and only one is a defect:**

1. **GENERATED config names -- not defects.** Confirmed by tracing: `bridge_4x4`
   comes from `bridge/bin/bridge_batch.csv`, `axi4_to_apb4` from
   `bridge_generator.py`, `delta_merge_2to1` from `complete_tree_generator.py`.
   A doc naming a config the generator emits is correct.
2. **PLANNED modules -- not defects.** `axi4_dwidth_converter` is the proven case:
   its page states "Location: Not implemented. Status: Planned - no RTL in this
   repository". Treating that as fabricated nearly destroyed a deliberate design
   document.
3. **Genuinely fabricated** -- names that are neither generated nor declared
   planned. Candidates with no generator and no `.sv`: `width_upsize_64_512`,
   `apbx_xbar_3to8`, `apbx_xbar_3to6`, `gaxi_fifo_sync_multi`,
   `gaxi_buffer_nfield`, `axi_apb_bridge`, `flexible_multiplier`,
   `address_decoder`, `arbiter_ar`, `arbiter_aw`, `response_router`,
   `delta_fanin_16to1`, `delta_fanout_1to16`, `pit_mode_fsm`, `simple_sram`,
   `axi_rom_wrapper`, `hive_top`, `rapids_top`, `delta_network_4x4`.

**Why it is not already a gate failure.** `bin/check_doc_examples.py` SKIPS a
block whose module does not resolve (`if mod not in index: continue`), so all 78
are invisible and the gate reads 0. Naming a ghost is therefore free, and fixing a
name makes the gate suddenly inspect the block -- so a rename without checking the
connections turns it red. That is not a reason to leave them; it is the reason
each needs classifying first.

**Resolves into:** per-area tasks for category 3, plus a decision on whether the
gate should report category 1/2 as *skipped-and-why* rather than silently. A gate
that skips 78 blocks while printing 0 is the blindness this area exists to catch.

**Note:** the port TABLES on those same pages are clean -- `docs/markdown` scores
0 bad across 6487 rows. This is specifically about fenced examples.
