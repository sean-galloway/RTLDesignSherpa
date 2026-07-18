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

# Write Data CAM (`pumice_wr_data_cam`)

**Module:** `pumice_wr_data_cam.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent:** `pumice_axi4_ifc`
**Status:** Implemented (fill / commit-drain / snarf movers)

> **Rearchitected:** the SWAG `wr_cmd_cam` was an ID-keyed metadata CAM with
> `w_buf_ptr` / `strb_ptr` pointers into an external AXI write buffer and a
> `b_pending` / `b_complete` window driven by `xbank_timers`. The live
> `pumice_wr_data_cam` **owns** the write-data SRAM and is keyed on
> `{bank, row, col}` with a free-running age. It has three data movers over the
> SRAM — **fill** (on insert), **snarf-stream** (read-your-write), and
> **commit-drain** (to DFI write) — plus associative query ports. Commit
> completion drives B directly (no external write-window timer). All movers are
> FIFO-fed with beat-counters — no active/slot FSM.

---

## Purpose

`pumice_wr_data_cam` holds every pending write: the decoded command key
`{bank, row, col}` **and** the burst data in an SRAM slot. It presents the
scheduler the same lookup/oldest interface as the read CAM so writes row-hit
schedule identically, forwards data to in-flight reads (snarf), streams committed
data to the DFI write path, and self-generates the B-completion strobe on evict.

## Parameters

| Parameter       | Default        | Purpose                                         |
|-----------------|----------------|-------------------------------------------------|
| `NUM_ENTRIES`   | 8              | In-flight write slots (`PTRW = $clog2`)         |
| `N_SCHED_LU`    | 4              | Parallel scheduler lookup ports                 |
| `NUM_BANKS`     | 8              | `BKW = $clog2(NUM_BANKS)`                        |
| `ROW_WIDTH`     | 14             |                                                 |
| `COL_WIDTH`     | 10             |                                                 |
| `AXI_ID_WIDTH`  | 8              | `IW`                                            |
| `AXI_DATA_WIDTH`| 64             | `DW` (the DFI word at the IFC); `SW = DW/8`     |
| `BL`            | 4              | Beats per burst (`BCW = $clog2(BL)`)            |
| `AGE_WIDTH`     | 16             | Free-running age counter width                  |
| `N_SRAM_SLOTS`  | `NUM_ENTRIES`  | SRAM data slots (may be `< NUM_ENTRIES`)        |

## Entry state (per slot)

| Field       | Description                                                             |
|-------------|-------------------------------------------------------------------------|
| `r_valid`   | Slot occupied                                                           |
| `r_bank` / `r_row` / `r_col` | Decoded command key                                    |
| `r_id`      | AXI ID (echoed on commit-done → B)                                     |
| `r_age`     | Insert-time snapshot of `r_age_ctr`                                    |
| `r_ptr` / `r_pv` | SRAM slot index (set on first fill beat) + its valid flag         |
| `r_fdone`   | **Fill complete** — set on the last fill beat. Only then may the entry be scheduled or snarfed (otherwise commit-drain could outrun a gapped fill and read stale SRAM beats). |
| `r_sched`   | Arbiter has committed this slot — excludes it from `sched_lu` / `oldest` the *next* cycle so the arbiter can pick another entry immediately (clean 1 cmd/clock). |

Relative age `w_rel[i] = r_age_ctr - r_age[i]` (wrap-safe). The data and strobes
live in distributed-RAM arrays `r_sram` / `r_strb`, each `N_SRAM_SLOTS*BL` deep.

## Age selectors

| Port              | Pick rule                              | Rationale                       |
|-------------------|----------------------------------------|---------------------------------|
| Snarf lookup      | **youngest** match (min `rel`)         | Latest data for a read          |
| Scheduler lookup  | **oldest** match (max `rel`)           | In-order commit per row         |
| Oldest port       | **oldest** valid (max `rel`)           | Scheduler fallback              |

All three selectors are gated on `r_valid && r_fdone && !r_sched`.

## Interfaces

### Insert (from `pumice_wr_intake` `aw_push`)

`ins_valid_i` / `ins_ready_o` with `{bank, row, col, id}`. `ins_ready_o` is
`w_have_free && u_fill_q.wr_ready`. On fire the slot is allocated (via the
priority-encoded free slot), key/id/age captured, and `r_fdone` cleared. The slot
index is pushed into the **fill FIFO** (`u_fill_q`, depth `NUM_ENTRIES`).

### Fill (from `pumice_wr_intake` `wdata` pop)

`wd_valid_i` / `wd_ready_o` with `{data, strb, last}`, written to SRAM in insert
order. The fill engine reads its slot from the fill-FIFO head:

- On the first beat (`r_fill_beat == 0`) a free SRAM slot is pre-allocated and
  recorded in `r_ptr[head]`; `wd_ready_o` requires a free slot on the first beat.
- Each beat writes `r_sram` / `r_strb` at `r_ptr[head]*BL + r_fill_beat`.
- On `wd_last_i` the entry's `r_fdone` is set and the fill FIFO popped.

### Snarf lookup + stream (from `pumice_rd_intake`)

`snarf_probe_*` returns a combinational `snarf_hit_o`. Read-your-write forwarding
is **limited to the safe case** — the hit requires all of:

1. `!r_sched` — a scheduled write is draining/evicting to DRAM, so its CAM data
   is racy.
2. `r_id == snarf_probe_id_i` — same-id W-before-R is the only AXI-ordered case
   where the read is *required* to see the write (cross-id has no ordering
   guarantee → that read takes the DRAM path).
3. `snarf_probe_len_i == BL-1` — every admitted write is exactly `BL` beats, so a
   short/long read must not snarf a full-BL write.

On `snarf_accept_i` (the read was admitted as a hit) the youngest matching slot
is pushed into a **snarf-request FIFO** (`u_snarf_q`). The snarf read engine
streams `snarf_rd_*` from `r_sram` at the FIFO-head slot, beat-counter
`r_sn_beat`, popping on the last beat.

### Oldest port + scheduler lookups

Same shape as the read CAM: `oldest_*` presents the oldest schedulable entry;
each of `N_SCHED_LU` ports returns the oldest `{bank, row}` match with its slot,
col, id, and age.

### Commit (from arbiter) + drain to DFI write

`commit_valid_i` / `commit_ready_o` / `commit_slot_i`. Commit **marks** the slot
`r_sched` (immediate exclusion) and enqueues it into the **drain FIFO**
(`u_drain_q`); `commit_ready_o` is the drain FIFO's write-ready. The commit-drain
read engine streams `cm_rd_*` (`{data, strb, last}`) from `r_sram` at the
drain-FIFO-head slot, beat-counter `r_cm_beat`, to the DFI write path. Marking is
decoupled from draining so the arbiter is never stalled by the DFI back-end.

### Commit-done → B

On the commit-drain last beat, `commit_done_valid_o` + `commit_done_id_o` strobe
the write intake's B-response path, and the entry is evicted:
`r_valid`/`r_pv`/`r_fdone`/`r_sched` cleared and the SRAM slot freed. There is no
separate `b_pending`/`b_complete` window and no `xbank_timers` completion driver —
completion is simply "the committed burst finished streaming to DFI."

## De-FSM'd sequencing

Each of the three movers (fill, snarf, commit-drain) is just a burst
beat-counter. The "active" slot for each is its request-FIFO head, stable until
popped on the last beat. There is no active/slot latch and no per-slot beats
counter beyond the shared engine counters.

## Difference from the read CAM

| Aspect          | Read CAM (`pumice_rd_cmd_cam`)              | Write CAM (`pumice_wr_data_cam`)                 |
|-----------------|--------------------------------------------|--------------------------------------------------|
| Data direction  | DFI return **in** → drain **out** to intake| Fill **in** from intake → commit **out** to DFI  |
| Movers          | return-fill + drain                        | fill + snarf-stream + commit-drain               |
| Forwarding      | none                                       | snarf (read-your-write) — the wr2rd path         |
| Extra flags     | `r_issued`, `r_ready`                       | `r_fdone`, `r_sched`                             |
| Completion      | AR-order drain to R channel                | commit-done strobe → B channel                   |

## Reset / busy

`ALWAYS_FF_RST` clears the age counter, all three beat-counters, `r_sram_occ`,
and per-entry `r_valid`/`r_pv`/`r_fdone`/`r_sched`. `busy_o` is oldest-found or
any request FIFO non-empty.

## Notes / flags

- The wr2rd (read-your-write) forwarding is **entirely** the snarf mover here;
  there is no standalone `wr2rd_forward` block in the live path (see
  [ch02/21](21_wr2rd_forward.md)).
- `N_SRAM_SLOTS` may be smaller than `NUM_ENTRIES`: an entry can exist in the CAM
  (key + age) before its SRAM slot is allocated on the first fill beat, so more
  commands can be tracked than there are data slots.
