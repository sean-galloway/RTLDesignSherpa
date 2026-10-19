# TASK-027: End-to-end credits and straps toward RAPIDS for the tile header

**Priority:** P2
**Status:** closed -- 2026-10-19
**Owner:** sean galloway

## Progress 2026-10-18

Items 1-3 are built behind `TILE_CREDITS` = 1 (needs `TILE_HDR`):
`rtl/fub/rapids_tile_credits.sv` in `rapids_src` (64 counters, each node's
internal and external ID, `rapids_pkg::tile_dest_index`), the `credit_*` path from
`rapids_tile_hdr_rx`, the per-packet charge in `src_data_path_axis`
(`tile_acq_*`), the scheduler's window hold and illegal-destination refusal,
and CSRs `SRC.TILE_ADV_WINDOW` / `TILE_LEGAL_DEST_LO` / `_HI` / `TILE_CREDIT_STATUS`.
Tests: `test_rapids_cxs_top.py::test_rapids_cxs_top_tile_credits[window,
no_oversend, shared_counter, node, illegal]` and the 16-channel
shared-counter cell, mutation-checked. The cell-side advertisement is delta
DELTA-010. Known limit: a channel reset does not refund charged credits.

Owner direction 2026-10-18: every node has an internal and an external ID
(the coordinate's `ext` bit, TILE_SPEC 11.3). delta nodes only transport and
never originate a packet on the data network (their own data goes on
MonBus): they never advertise or return credits and consume what is
addressed to them on arrival. So a node's internal ID is legal by topology
and never charged, and a read request to a node is refused (built
2026-10-18). Only the external IDs (cells, control cores) carry credits, and
each cell or core sends its own boot advertisement.

Owner direction 2026-10-18 (TILE_SPEC 11.14): delta must carry result data
to `level` 3. Toward RAPIDS the credits are **straps, not grants**: a cell
writes against a 16-flit strap, a control core (gatling, which creates the
descriptors) sends `desc` against strapped descriptor-queue entries.

## Progress 2026-10-19: straps toward RAPIDS (items 2-10)

Built behind `TILE_CREDITS` = 1:

- **Landing space** `rtl/fub/rapids_tile_landing.sv` in `rapids_snk`: one
  `TILE_LAND_FLITS`-deep FIFO per cell (external slots 0-15,
  `rapids_pkg::tile_ext_slot`). A whole packet drains only when its sink
  channel can take it (`snk_data_path_axis.chan_can_take`, room >=
  `TILE_LAND_FLITS`+4), so a cell blocked on a full channel holds only its
  own strap. Disabled or out-of-range channels are drained and discarded.
- **Returns** `rtl/fub/rapids_tile_credit_tx.sv` in `rapids_core`: pending
  counts per {slot, class}, sent round-robin as soon as the output is free
  (coalescing only what is already pending), header-only `credit` packets on
  their own port `m_tile_credit_*`. Class 0 = flits (each landing beat, each
  charged header, each discarded beat); class 1 = intake entries.
- **Descriptor intake** `rtl/fub/rapids_tile_desc_intake.sv`
  (4 x `TILE_DESC_PER_CORE` deep); `descriptor_engine_shared` gains `INJ_HOLD`
  so a desc for a busy channel waits instead of being dropped. The entry's
  credit returns when it moves into the descriptor queue; an overrun drop
  still returns it.
- **Resync** `SRC.TILE_RESYNC.GO`: waits for `tile_quiescent`, then one `set`
  per legal cell (LAND_FLITS) and core (DESC_PER_CORE). Channel resets are
  also gated by `tile_quiescent`.
- **Stall checks** `rtl/fub/rapids_tile_stall_mon.sv`, threshold
  `SRC.TILE_STALL_CYCLES` (default 1000, 0 = off): sink data that has not
  moved (agent 0x0B), source reads outstanding with no data (agent 0x0C);
  `PktTypeError` / `PROTOCOL_CORE` / `RAPIDS_EVENT_STALL` (0x08) on MonBus,
  once per episode; `SRC/SNK.TILE_STALLED.CH`.
- Status: `TILE_CREDIT_STATUS` RESYNC_BUSY / LAND_OVERRUN / INTAKE_OVERRUN /
  RET_COUNT.

Tests: `test_rapids_cxs_top.py::test_rapids_cxs_top_tile_straps[land,
land_isolation, land_discard, coalesce, intake, intake_overrun, resync,
quiescent_reset, stall_sink, stall_source]` and
`test_rapids_16ch_cxs_top_tile_straps` (isolation); TB
`dv/tbclasses/rapids_cxs_tile_straps_tb.py`.

Mutations (all restored, cmp-verified):

| Mutation | Caught by |
|---|---|
| M1 no landing-beat return | land (16 flits sent, 2 returned) |
| M2 drain ignores chan_can_take | land_isolation |
| M3 no charged-header return | land (48 sent, 42 returned) |
| M4 INJ_HOLD off (desc dropped) | intake_overrun |
| M5 resync ignores quiescent | resync |
| M6/M6b channel resets ungated | quiescent_reset |
| M7 old has_data formula | stall_sink (2 records) |
| M8 source pending forced 0 | stall_source |
| M9 no intake-pop return | intake |
| M10 disabled channel not drained | land_discard (same build as M1, not isolated) |

Bug found on the way: `chan_has_data` counted an allocated-but-unfilled SRAM
segment as data, so the sink stall check fired twice (M7 reproduces it).

Regression: clean-all `run-all-full-parallel` over fub, fub_beats, macro,
macro_beats, top, top_beats: 1722 + 1284 + 843 + 774 + 162 + 54 = 4839
passed, 0 failed (2026-10-19).

Docs: MAS 3.14 "Straps Toward RAPIDS" (tables 3.14.4 / 3.14.5), HAS
Descriptor Format strap paragraph, rapids CLAUDE.md.

Deviations from TILE_SPEC: resync sends one `set` per sender, not a
multicast (RAPIDS has no multicast header); stall checks are RAPIDS-local
rather than a shared ocelus module. Limits: read replies into RAPIDS are not
strap-accounted; only cells hold landing space (cores send only `desc`).

Remaining: the TILE_SPEC 11.12 row (still says the straps are not built).

## What to build

1. Done: 64 counters, advertisement window, legal mask, credit intake (above).
2. **Landing space** (owner 2026-10-18: a parameter, `TILE_LAND_FLITS`,
   default 16): one per sender, so a cell whose data targets a full sink
   channel holds only its own strap. A packet to RAPIDS is at most
   `TILE_LAND_FLITS` flits.
3. **Credit returns from RAPIDS** (owner: a must): `credit`/`add` to the
   sender when its data leaves the landing space for its sink channel, and
   when a `desc` entry leaves the intake queue.
4. **Descriptor intake** (owner 2026-10-18): there is one descriptor queue
   (the put side of `descriptor_engine_shared`, which already muxes the fetch
   path and the TILE_HDR injection). A `desc` intake FIFO as deep as the
   descriptor credits handed out (a parameter) is muxed into that put; an
   entry's credit returns when it moves into the descriptor queue.
5. **Resync** after root failover (TILE_SPEC 11.10): `set` to every cell and
   core restoring its strap.
6. **Deadlock:** resolved by construction (owner 2026-10-18): credits have
   their own interfaces, so a credit never waits behind data.
7. **Always return credits** (owner 2026-10-18), including for a packet
   RAPIDS discards (bad header, bad tag, disabled channel).
8. **ocelus stall checks**, 10 us (a cycle threshold), error on MonBus:
   sink, data in the sink SRAM that has not moved; source, a channel
   expecting data (reads outstanding) whose SRAM has received none. The
   scheduler's existing `cfg_sched_timeout_*` watches write-engine grant
   progress, not data arrival, so it does not cover the source case.
9. **Prompt returns**: coalesce only what is already pending; never hold
   credits to build a batch while the sender may be waiting.
10. **Quiescent gating**: resync, resets and partial resets happen only
    under the global quiescent signal (TILE_SPEC 9, 11.10).

Owner rulings 2026-10-18: strap and parameter agreement is a Hive-level
contract (the Hive sets and checks it), so RAPIDS adds no cross-check of
the cells' straps or packet lengths. A duplicated `add` is a user error, not
a RAPIDS guard. With the scheduler refactor each scheduler keeps a two-deep
descriptor skid buffer, which absorbs a `desc` for a busy channel at the
head of the intake FIFO.

## Done when

- Tests: a cell model that advertises (`set`), returns credits after
  consuming, and sends only against its strap; RAPIDS never oversends a
  destination, cell or node; concurrent channels to one cell share its
  counter; a node is never charged and never advertises; a descriptor entry is consumed and returned; a spare index and a
  destination that never advertises end the window illegal, and a descriptor
  to either is refused.
- TILE_SPEC 11.12 updated; HAS/MAS chapters; byte regression clean-all FULL.

## Closure (2026-10-19)

Closed by the owner 2026-10-19. Items 1-10 are built and tested (ddba1af95;
full clean-all regression 4839/4839). The TILE_SPEC 11.12 row, the one
"Done when" item not done, moved to rapids TASK-031 together with how the
straps are set on RAPIDS.
