# TASK-009: 07_beats_latency_bridge.md documents the wrong CONCEPT

**Priority:** P1. Prioritised by the rapids session; misleads worse than a wrong name.
**Status:** open 2026-09-26.

**The page describes a beat-count/ID bridge. The module is a data-width skid.**

| Page says | `latency_bridge_beats.sv` actually has |
|---|---|
| `in_valid`, `in_ready`, `in_beats`, `in_id` | `s_valid`, `s_ready`, `s_data` |
| `out_valid`, `out_ready`, `out_beats`, `out_id` | `m_valid`, `m_ready`, `m_data` |
| params `DEPTH`, `BEATS_WIDTH`, `ID_WIDTH`, `REGISTERED` | params `DATA_WIDTH`, `SKID_DEPTH`, `DW` |
| -- | `occupancy` [2:0], `dbg_r_pending`, `dbg_r_out_valid` |

**Why this needs re-authoring, not a table patch.** The Input/Output tables, the
integration example, Figure 2.7.1 and the timing diagram all describe the same
non-existent interface. Correcting only the tables leaves the page contradicting
itself. Its example also instantiates three ghost modules
(`beats_alloc_ctrl`, `beats_latency_bridge`, `beats_drain_ctrl`) and connects
`.wr_size(fill_size)` / `.rd_size(axi_drain_size)` against signals not in scope.

**Not going away.** The rapids session confirmed `latency_bridge_beats` keeps its
test, its filelist and its `rapids_all.f` entry -- it only left the SRAM path
(note already added to the page in `d587852c2`).

**Gate interaction, important.** The page's example is currently INVISIBLE to
`bin/check_doc_examples.py` because its module names do not resolve, so the gate
skips the block. Fixing the module name WITHOUT the connections turns the gate
red. Do both in one edit.

**Done when:** tables, parameters, example and both figures agree with
`latency_bridge_beats.sv`, and `check_doc_examples.py` stays at 0.

**Related:** [[TASK-007]], [[TASK-010]]
