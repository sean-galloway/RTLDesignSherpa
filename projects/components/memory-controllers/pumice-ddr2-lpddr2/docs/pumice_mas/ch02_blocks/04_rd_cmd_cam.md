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

# Read Command CAM (`pumice_rd_cmd_cam`)

**Module:** `pumice_rd_cmd_cam.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent:** `pumice_axi4_ifc`
**Status:** Implemented (de-FSM'd streaming drain)

> **Rearchitected:** the SWAG CAM was keyed by AXI ID and drove a `match_pending`
> vector with per-slot beat counters and an issue FSM. The live
> `pumice_rd_cmd_cam` is keyed by `{bank, row}` with a free-running age, exposes
> `N_SCHED_LU` parallel scheduler lookups plus an oldest port, and is a **read
> reorder buffer**: DRAM read data returns in *issue* order into per-entry SRAM
> slots and drains to the intake in *AR (insert)* order. The drain has **no**
> active/slot state latch — a burst beat-counter and the combinational
> oldest-valid pick are the only sequencing.

---

## Purpose

`pumice_rd_cmd_cam` tracks every outstanding DRAM read (the MISS path — snarf
hits never enter this CAM). It is the mirror of `pumice_wr_data_cam` on the issue
side, but the data direction is opposite: data comes **in** from the DFI read
return and drains **out** to `pumice_rd_intake`. There is no snarf port (that is
a write-CAM concept).

It acts as a reorder buffer because DRAM read data returns in the order the
scheduler *issued* commands (which is row-hit reordered), whereas the AXI R
channel must see reads in AR order. Data is buffered per entry, then released
oldest-first once complete.

## Parameters

| Parameter       | Default        | Purpose                                         |
|-----------------|----------------|-------------------------------------------------|
| `NUM_ENTRIES`   | 8              | In-flight read slots (`PTRW = $clog2`)          |
| `N_SCHED_LU`    | 4              | Parallel scheduler lookup ports                 |
| `NUM_BANKS`     | 8              | `BKW = $clog2(NUM_BANKS)`                        |
| `ROW_WIDTH`     | 14             |                                                 |
| `COL_WIDTH`     | 10             |                                                 |
| `AXI_ID_WIDTH`  | 8              | `IW`                                            |
| `AXI_DATA_WIDTH`| 64             | `DW` (the DFI word at the IFC)                  |
| `BL`            | 4              | Beats per burst (`BCW = $clog2(BL)`)            |
| `AGE_WIDTH`     | 16             | Free-running age counter width                  |
| `N_SRAM_SLOTS`  | `NUM_ENTRIES`  | SRAM data slots (may be `< NUM_ENTRIES`)        |

## Entry state (per slot)

| Field       | Description                                                    |
|-------------|----------------------------------------------------------------|
| `r_valid`   | Slot occupied                                                  |
| `r_issued`  | Scheduler has issued this read to DRAM                         |
| `r_ready`   | Data complete (last DFI return beat seen)                      |
| `r_bank`    | Decoded bank (key)                                            |
| `r_row`     | Decoded row (key)                                             |
| `r_col`     | Decoded column                                               |
| `r_id`      | AXI ID (echoed on drain)                                      |
| `r_resp`    | Captured DFI return response                                  |
| `r_age`     | Insert-time snapshot of `r_age_ctr`                          |
| `r_ptr` / `r_pv` | SRAM slot index (set on first return beat) + its valid flag |

Relative age is `w_rel[i] = r_age_ctr - r_age[i]` (wrap-safe); larger `rel` =
older. The burst data lives in a distributed-RAM array `r_sram[N_SRAM_SLOTS*BL]`.

## Interfaces

### Insert (from `pumice_rd_intake` `ar_push`, AR order)

`ins_valid_i` / `ins_ready_o` with `{bank, row, col, id}`. `ins_ready_o` is
`w_have_free` (any `!r_valid[i]`). On fire the slot is allocated, `r_issued` /
`r_ready` cleared, key/id captured, and `r_age <= r_age_ctr`.

### Scheduler lookups (N, keyed `{bank, row}`)

For each of `N_SCHED_LU` ports the CAM returns the **oldest NOT-ISSUED** entry
matching `{bank, row}` (max `rel` among `valid && !issued`), with its slot, col,
id, and age. This lets the arbiter row-hit-schedule reads exactly like writes.

### Oldest not-issued port

`oldest_valid_o` + `{bank, row, col, id, slot}` — the oldest `valid && !issued`
entry, the arbiter's fallback ACT target.

### Issue notify

`issue_valid_i` / `issue_ready_o` / `issue_slot_i`. The scheduler tells the CAM
which slot it issued. On fire, `r_issued[slot] <= 1` **and** the slot is pushed
into an **issue-order FIFO** (`u_issue_q`, depth `NUM_ENTRIES`) so returns fill
the right slot in issue order.

### DFI read return (data in, issue order)

`dfi_ret_valid_i` / `dfi_ret_ready_o` with `{data, resp, last}`. The return-fill
engine writes each beat into the SRAM slot of the **issue-FIFO head**
(`w_iq_rd_slot`):

- On the first beat (`r_ret_beat == 0`) it pre-allocates a free SRAM slot
  (`w_slot_free`) and records it in `r_ptr[head]`, marking `r_sram_occ`.
- `dfi_ret_ready_o` is gated on the issue FIFO being non-empty and (first-beat
  only) a free SRAM slot existing.
- On `dfi_ret_last_i` the entry is marked `r_ready`, `r_resp` captured, and the
  issue FIFO popped (`w_iq_rd_ready`).

### Drain to `pumice_rd_intake` (AR order, oldest-first, ready-gated)

`drain_valid_o` / `drain_ready_i` with `{data, id, resp, last}`. The draining
slot **is** the combinational oldest-valid pick `w_dro_slot` (max `rel` among all
`valid`), which is stable across a burst: the entry stays valid until its own
last-beat evict, and later inserts are always younger, so no other entry can
become "more oldest" mid-burst. Drain is enabled when
`w_dr_go = oldest-found && r_ready[oldest]` (data staged). Only a burst
beat-counter `r_dr_beat` is registered; `drain_last_o = (r_dr_beat == BL-1)`.

## De-FSM'd sequencing

There is **no** active/slot FSM on the return or drain path. The return path
targets the issue-FIFO head; the drain path targets the oldest-valid pick. Both
"active" slots are combinational functions of registered state and remain stable
until their burst's last beat. The only registered burst state is the two
beat-counters (`r_ret_beat`, `r_dr_beat`) plus the age counter and per-entry
flags. This mirrors the write CAM and removes the SWAG's issue FSM entirely.

## Eviction

On the drain last beat (`w_dr_fire && drain_last_o`): `r_valid[oldest] <= 0`,
`r_pv` cleared, `r_dr_beat` reset, and the SRAM slot freed
(`r_sram_occ[r_ptr[oldest]] <= 0`). AR-order release is a natural consequence of
always draining the oldest entry.

## Reset

`ALWAYS_FF_RST(aclk, aresetn, ...)`: clears `r_age_ctr`, both beat-counters,
`r_sram_occ`, and per-entry `r_valid` / `r_issued` / `r_ready` / `r_pv`. `busy_o`
is `oldest-found || issue-FIFO non-empty`.

## Notes / flags

- Reads are keyed on `{bank, row}` only (not AXI ID); ID is carried for the R
  echo and drained with the data. There is no per-ID beat table.
- The `drain_id_o` port is driven but left unconnected at the IFC (the intake's
  order FIFO already carries the R-channel id); `oldest_id_o` and
  `sched_lu_id_o` are likewise informational — the arbiter's `unused` sink
  absorbs the id/slot buses it does not consume.
- No CSR/QoS priority in this CAM — selection is purely by wrap-safe age.
