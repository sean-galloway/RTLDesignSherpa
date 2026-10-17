# TASK-026: Cell-issued descriptors into the source half (the `desc` path)

**Priority:** P2
**Status:** active
**Owner:** sean galloway

A tile cell can hand RAPIDS a complete 256-bit source descriptor; RAPIDS reads
the memory it names and sends the data to the cell (or any cell) the
descriptor addresses -- a cell-initiated pull. Owner request 2026-10-16. The
protocol is defined in `projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md`
Section 11.11 (proposal); this task is the RAPIDS side.

## What to build

1. **Sink port recognises `desc`.** A packet with header `ptype` = 4 (`desc`),
   destination `level` 3, carries one source descriptor. It is never written
   to a sink channel's SRAM; it goes to the source half instead. Depends on the
   tile packet header (TILE_SPEC 11.5) being implemented in the CXS planes.
2. **Sink-to-source path.** A path from the sink half to the source half,
   carrying {source channel = header tag, 256-bit descriptor}. The credit
   returns of TILE_SPEC 11.9 need the same path; build it once.
3. **Second write port into the source channel's descriptor queue.** In
   `descriptor_engine_shared` (SHARED_ENGINES=1) the queue is already per
   channel; add an injection write beside the R-path write, arbitrated with
   it, counted by the prefetch throttle. An idle channel starts on the
   injected descriptor as if kicked with it already fetched; a busy one runs
   it after what is queued. A non-zero next pointer chains into memory as
   usual. Decide whether SHARED_ENGINES=0 supports it or the path requires 1.
4. **Descriptor-slot grants.** Credit class 1 (TILE_SPEC 11.9 / 11.11):
   RAPIDS grants a cell N descriptor slots for a source channel and returns a
   slot when the scheduler takes the descriptor. A `desc` packet arriving
   without a slot is a protocol error (sticky status), never a stall.
5. **Source descriptor fields.** The proposed `ptype` [215:213], `op` [216]
   and the destination coordinate / target address in `dst_addr` (RAPIDS HAS,
   Descriptor Format) must exist for the source half to build the outgoing
   header; this task needs them, or lands with them.

## Open decisions (owner)

- A source channel reserved for cell-issued descriptors, or any channel the
  tag names.
- Whether the issuing cell is told when its pull completes (it sees the data
  when it pulls to itself; nothing tells it when it pulls to another cell).
- Range checking of `src_addr` on cell-issued descriptors (host-built ones
  are not checked today).

## Done when

- Tests: a cell model (the planned RapidsSrcTile / RapidsSnkTile / cell
  classes in `dv/tbclasses/`) issues descriptors on several channels
  concurrently, idle and busy, including one that chains into memory; data
  arrives at the addressed cells; a `desc` without a grant raises the error;
  channel reset with an injected descriptor queued.
- HAS/MAS updated, TILE_SPEC 11.11 moved from proposal to defined for the
  RAPIDS side; full byte regression clean-all FULL green.

## Progress (2026-10-17)

Built behind `TILE_HDR` = 1 (byte tree; needs `SHARED_ENGINES` = 1), with the
tile header of TILE_SPEC 11.5 on both ports (TILE_SPEC 11.12 has the status table):

- Items 1, 2, 3 and 5 are done. `rtl/fub/rapids_tile_hdr_rx.sv` decodes the sink
  port; `rapids_core` carries `desc_inj_*` from the sink half to the source half;
  `descriptor_engine_shared` (INJ_EN) has the second writer: a one-descriptor slot
  per channel, drained into the queue while the channel's fetch side is idle; the
  scheduler and `src_data_path_axis` build the outgoing header.
- Item 4 (descriptor-slot grants) is NOT built. The slot stands in for it: a `desc`
  with no free slot is dropped and sets the channel's sticky `sts_tile_desc_dropped`
  bit; the channel carries on (an RTL review found the first cut errored the channel
  and killed its running transfer). Grants arrive with the end-to-end credits
  (TILE_SPEC 11.9 / 11.10), not built either.
- RTL review 2026-10-17 (3 HIGH, 3 MEDIUM, 4 LOW) fixed: owed-beat guard on the
  injection write; non-fatal drops; source `ptype` > mem refused; data headers wait
  for their first data beat; header-only packets alternate with data pops; drops
  during channel reset flagged. The sink-stream = tag rule is in TILE_SPEC 11.12.
- Open decisions taken as defaults: any channel the tag names; no completion
  notice to the issuing cell; `src_addr` not range-checked (as for host
  descriptors).
- Tests: seven `test_rapids_cxs_top_tile_*` cells (source write, read request, sink
  write, cell descriptors idle/busy/chained on four channels, slot overflow, source
  ptype refusal, credit/unsupported), each mutation-checked. Not covered by a test:
  the owed-beat guard (reset mid-fetch then inject) and header/pop fairness.
- Still to do for "Done when": grants, the MAS chapters, a CSR for `sts_tile_*`.
