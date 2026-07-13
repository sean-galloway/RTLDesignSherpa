<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Transaction Queue (retired — replaced by the two command CAMs)

> ## RETIRED — no standalone FUB
>
> The unified transaction queue (`txn_queue_fub`) described by the SWAG was
> **never built as a separate block**. The scheduling-view function it was meant
> to provide is delivered directly by the two command CAMs:
>
> - **Pending writes** live in [`pumice_wr_data_cam`](05_wr_cmd_cam.md) —
>   `{bank, row, col}` key, free-running age, and the burst data in SRAM.
> - **Pending reads** live in [`pumice_rd_cmd_cam`](04_rd_cmd_cam.md) —
>   `{bank, row}` key, free-running age, per-entry return buffering.
> - **Per-direction completion** is FIFO-based in the intakes
>   ([`pumice_wr_intake` / `pumice_rd_intake`](02_axi4_slave.md)): the write B
>   FIFO and the read order + rd-data FIFOs.
>
> This chapter is retained to document *where the queue's responsibilities went*
> and *why*. The SWAG's entry-format, four-state lifecycle, `cam_slot_idx`
> reverse pointer, and `row_hit_cached` broadcast are all superseded and should
> not be treated as the current architecture.

**Status:** Retired

---

## What the CAMs do instead

The SWAG separated a narrow "scheduling view" (the queue) from a wide "metadata
view" (the CAMs) to keep the scheduler's per-cycle comparator fan-in small. The
live design collapses the two: each CAM entry carries **both** the scheduling key
and the metadata, and the scheduler reads the CAMs directly through purpose-built
lookup ports rather than a wide parallel-entry snapshot.

### Scheduler visibility (replaces the parallel `q_entries` bus)

Instead of a wide per-entry snapshot bus, each CAM exposes:

- **`N_SCHED_LU` lookup ports** (`N_LU = NUM_BANKS`, one per bank). The arbiter
  drives each port with `{bank j, that bank's open row}` and the CAM returns the
  oldest matching not-yet-committed entry — slot, column, id, and age. This is
  the row-hit query that used to be the `row_hit_cached` field.
- **An `oldest` port** — the oldest schedulable entry, used as the arbiter's ACT
  fallback target.

The scheduler thus gets exactly the row-hit and fallback candidates it needs,
computed inside the CAM combinationally, with no separate queue structure and no
`row_hit_cached` coherency broadcast.

### Entry lifecycle (replaces FREE/PENDING/ISSUED/COMPLETING)

The four-state queue lifecycle is replaced by per-entry flags in each CAM:

| SWAG queue state | Live equivalent (write CAM)         | Live equivalent (read CAM)          |
|------------------|-------------------------------------|-------------------------------------|
| FREE             | `!r_valid`                          | `!r_valid`                          |
| PENDING          | `r_valid && r_fdone && !r_sched`    | `r_valid && !r_issued`              |
| ISSUED           | `r_sched` (enqueued to drain FIFO)  | `r_issued` (enqueued to issue FIFO) |
| COMPLETING       | commit-drain streaming, then evict  | data returning, then oldest-drain   |

The exclusion of already-committed/issued entries from the lookup/oldest ports
(`r_sched` on the write side, `r_issued` on the read side) is what guarantees the
arbiter never picks the same slot twice — the role the `pick_valid_mask` played
in the SWAG.

### Age (replaces the saturating `age` counter)

Both CAMs use a free-running `AGE_WIDTH` counter and wrap-safe relative age
(`rel = age_ctr - entry_age`). Oldest = max `rel`. There is no saturation, no
`AGE_MAX` parameter, and no `age_max_runtime` CSR clip; wrap-safety makes
saturation unnecessary.

### Backpressure (replaces `q_high_water` / `q_full`)

There is no queue occupancy watermark. Backpressure is structural: the write path
stalls when the wr-data CAM has no free entry or its fill FIFO is full; the read
path stalls when the rd-cmd CAM is full or the intake's order FIFO is full. The
AXI channels back-pressure through the intake FIFOs.

## Why the split disappeared

The queue existed to make a *single* wide scheduling snapshot cheap. Once the
scheduler was rearchitected to query per-bank (one lookup per open row) rather
than scan every entry, the wide snapshot was no longer needed — the CAM's own
associative match is the scheduling view. Keeping a second copy of
`{rank, bank, row}` in a queue, plus the `cam_slot_idx` reverse pointer and the
`row_hit_cached` broadcast coherency machinery, would have been pure overhead.

See [ch02/07](07_scheduler.md) for the arbiter that consumes the CAM lookup
ports and [ch02/04](04_rd_cmd_cam.md) / [ch02/05](05_wr_cmd_cam.md) for the CAM
internals.
