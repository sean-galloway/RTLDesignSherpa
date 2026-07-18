# pumice_axi4_ifc — write/read front-end µarch (locked spec)

Reference for correctness at every boundary is **JEDEC DDR2 + DFI 2.1** (see
`init_sequencer`/`dfi_cmd_formatter` for the command side). This doc covers the
AXI4 host face: two dumb intake FUBs + the shared snarf contract.

## Guiding decisions

- **1 AXI burst ≡ 1 DFI burst.** The host (or the front splitter) sizes bursts so
  `(awlen+1) × GEAR == BL`. No splitting/merging inside the intakes.
- **In-order commit.** No per-burst or cross-burst write reordering. The data
  buffer is a plain FIFO, not a pointer-addressed RAM. This deletes the historic
  out-of-order-completion / overwrite bug surface entirely.
- **Snarf (read-your-writes) lives in the CAM**, not in the intake. The intake is
  dumb; the wr-data CAM (the *next* FUB, downstream) owns addressing + snarf.
- **Splitter is an external bolt-on** for arbitrary host bursts:
  `axi_master_wr_splitter` / `axi_master_rd_splitter` with
  `alignment_mask = DRAM_burst_bytes − 1` (each split ≤ one DRAM burst; W split,
  B/R responses consolidated to one per original host burst). Reused as-is.

## FUB 1 — pumice_wr_intake (dumb)

```
s_axi_aw/w/b (post-split, BL-sized)
  → axi4_slave_wr (skid/protocol)
  → AW-meta FIFO   : {addr, id}            (gaxi_fifo_sync)
  → wr-data FIFO   : {data, strb, last}    (gaxi_fifo_sync, per-AXI-beat; GEAR
                                            repack deferred to the DFI data path)
  → addr_mapper    : addr → {rank,bank,row,col}
out: aw_push_valid/ready + {rank,bank,row,col,id}   (to the wr-data CAM)
     wdata pop      valid/ready + {data,strb,last}   (drained in commit order)
```
- **Guardrail:** assert `(awlen+1)×GEAR == BL` in sim; `bresp = SLVERR` on a
  mismatched (ragged) burst on silicon. No pointer, no CAM, no forwarding here.
- One B per burst (splitter consolidates to one per host AW).

## FUB 2 — pumice_rd_intake (dumb + snarf, mirror of FUB 1)

```
s_axi_ar/r (post-split)
  → axi4_slave_rd
  → AR-meta FIFO : {addr, id}
  → addr_mapper  : addr → {rank,bank,row,col}
  → SNARF PROBE at the AR inlet: look {bank,row,col} up in the wr CAM
       HIT  → capture youngest-match write data in order into the AR queue;
              tag source = snarf
       MISS → tag source = DFI; issue ar_push to the scheduler
  → rd-data FIFO : {data, id, last, resp}   → AXI R channel
  → SOURCE ARBITER fills rd-data FIFO in AR order, per read, from either
       the DFI read-return path OR the snarf path.
```
- **CAM hit forces snarf** (DRAM is stale for in-flight writes) — not optional.
- Probe **at the AR inlet** fixes the ordering point (a later write can't affect
  an already-probed read).
- **Youngest-match** on snarf (CAM oldest/youngest selector = youngest).
- **In-order R return**: a snarf-ready read waits behind an earlier DFI read.
- Replaces the old `wr2rd_forward` + `rd_inject`/`fwd` paths entirely.

## pumice_wr_data_cam (inside the ifc)

Entry: `{ valid, bank, row, col, id, age[15:0], ptr, ptr_valid }`.
`age` captured on insert. **`ptr` (into the wr-data SRAM) is written on the FIRST
data beat**, not at insert — SRAM allocation is decoupled from CAM allocation. A
separate **`sram_occ[N_SRAM_SLOTS]`** bit-vector (1=occupied) pre-allocates the
BL-group slot on first write and frees it on evict, so `N_SRAM_SLOTS` can be fewer
than tracked entries. (Both CAMs share this pattern; the rd CAM allocates its slot
on the first DFI-return beat.)

TODO (splits): when the front splitter turns one host burst into N DRAM bursts,
an **aggregator** is needed to reassemble them into one host burst/response. Not
built under the dumb 1:1 contract.

Ports:
- **insert** (from `pumice_wr_intake`): `aw_push{bank,row,col,id}` allocates a free
  slot + captures age; the burst's BL beats stream from the wr-data FIFO into
  `wr-data-SRAM[slot]`.
- **snarf lookup** (from `pumice_rd_intake`): associative by `{bank,row,col}`,
  returns hit + the **youngest** matching slot (WAW → newest data); the burst is
  streamed out of `wr-data-SRAM[slot]`. Non-destructive.
- **oldest-entry port (dedicated, always-on)**: continuously presents the OLDEST
  valid entry `{valid,bank,row,col,id,ptr}` (min age). This is the **scheduler's
  fallback**: the scheduler issues several parallel lookups in one cycle; if they
  all miss it schedules this always-available oldest entry — no sequential search,
  guaranteed forward progress.
- **evict/commit**: free a slot by index once its write has committed to DFI
  (`wr_beat_sequencer` reads `wr-data-SRAM[slot]` for the BL beats first).

**Scheduler lookup ports** — `N_SCHED_LU` generic parallel query ports (param, not
tied 1:1 to banks). Each: in `{valid, bank, row}` → out `{hit, slot, col, id, age}`
= the **oldest** matching entry for `{bank,row}` (in-order per row; mirror of
snarf's youngest). Consumed by the `command_scheduler`: it fires all N in one
cycle, picks the globally-oldest hit (issue WR, no ACT), and **falls back to the
`oldest` port** when all N miss. The chosen `slot` is driven back on `commit_slot`
to evict after the write commits. These are external ports of `pumice_axi4_ifc`.

## pumice_rd_cmd_cam (inside the ifc — mirror, for consistency)

Tracks outstanding DRAM reads (the MISS path). Allocated on `ar_push`, matched by
the returning DFI read data, and feeds the **DFI side of the source arbiter** in
`pumice_rd_intake`. (In-order commit ⇒ this can be a FIFO-ordered tracker; kept as
a CAM for symmetry / future read reorder — nail the internal form when we build it.)

## FUB 3 — pumice_axi4_ifc (holds BOTH intakes + BOTH CAMs)

```
host AXI4 → [wr/rd splitter] → pumice_wr_intake ─┐
                             → pumice_rd_intake ─┤
   pumice_wr_data_cam  (snarf source, wr commit) ┘
   pumice_rd_cmd_cam   (outstanding-read tracker, DFI-read side of arbiter)

external ports:  host AXI4 (pre-split);
                 command stream → scheduler (writes + reads);
                 wdata commit pop → wr_beat_sequencer;
                 DFI read-return in ← rd datapath / rd_cl_aligner
```

## Test plan (Pattern B, projects/ area)

- **wr_intake**: BL-sized writes → check `aw_push{rank,bank,row,col,id}` decode +
  wr-data FIFO pops {data,strb,last} + one B; ragged burst → SLVERR/assert.
- **rd_intake**: MISS → ar_push + drive DFI-read source → check R; HIT → drive
  snarf-probe hit+data → check R from snarf; interleave to prove in-order arbiter.
- **pumice_axi4_ifc**: arbitrary host bursts → splitter → intakes; write then read
  the same address → **real snarf** through the internal wr CAM (no mock); MISS read
  serviced via the internal rd CAM + a mocked DFI read-return; B/R consolidated to
  one per host burst.
