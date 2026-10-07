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

# Write Data CAM (`scoria_wr_data_cam`)

**Module:** `scoria_wr_data_cam.sv`
**Location:** `rtl/fub/`
**Category:** write scheduling window + data SRAM
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified

---

## Purpose

The write-data CAM holds pending write commands keyed on `{bank,row,col}` and stores each burst's data in a dedicated SRAM slot. It is a scheduling window, a data buffer, a read-your-write bypass, and a rate-matched drain all in one: fill writes W beats into SRAM, snarf streams them back to a matching read, and commit streams them to the DFI write path.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_ENTRIES` | int | 1+ | 8 | CAM scheduling-window entries |
| `N_SCHED_LU` | int | 1+ | 4 | scheduler lookup ports |
| `NUM_BANKS` | int | 1+ | 8 | DRAM banks |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `COL_WIDTH` | int | — | 10 | column address width |
| `AXI_ID_WIDTH` | int | — | 8 | AXI ID width |
| `AXI_DATA_WIDTH` | int | — | 64 | AXI data width |
| `AXI_BEATS_PER_BURST` | int | power of 2 | 4 | beats per burst |
| `AGE_WIDTH` | int | — | 16 | free-running age counter width |
| `N_SRAM_SLOTS` | int | 1+ | `NUM_ENTRIES` | SRAM slots (may be less than `NUM_ENTRIES`) |
| `WR_DRAIN_AHEAD` | int | 1+ | 2 | bursts allowed in commit-drain queue |

: Table 2.7.1: Write data CAM parameters

## Interface

### Command insert

| Signal | Direction | Width | Description |
|---|---|---|---|
| `ins_valid_i` | in | 1 | allocate a CAM entry |
| `ins_ready_o` | out | 1 | entry can be allocated |
| `ins_bank_i` | in | `BKW` | command bank |
| `ins_row_i` | in | `ROW_WIDTH` | command row |
| `ins_col_i` | in | `COL_WIDTH` | command column |
| `ins_id_i` | in | `AXI_ID_WIDTH` | command ID |
| `ins_qos_i` | in | 4 | command QoS |
| `ins_agg_i` | in | 1 | part of a split host burst |
| `ins_last_i` | in | 1 | final sub of the split host burst |

### Fill data

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wd_valid_i` | in | 1 | W data valid |
| `wd_ready_o` | out | 1 | CAM ready for W data |
| `wd_data_i` | in | `AXI_DATA_WIDTH` | W data |
| `wd_strb_i` | in | `AXI_DATA_WIDTH/8` | W strobe |
| `wd_last_i` | in | 1 | W last |

### Snarf lookup and stream

| Signal | Direction | Width | Description |
|---|---|---|---|
| `snarf_probe_valid_i` | in | 1 | read probe valid |
| `snarf_probe_bank_i` | in | `BKW` | probe bank |
| `snarf_probe_row_i` | in | `ROW_WIDTH` | probe row |
| `snarf_probe_col_i` | in | `COL_WIDTH` | probe column |
| `snarf_probe_id_i` | in | `AXI_ID_WIDTH` | read AXI ID |
| `snarf_probe_len_i` | in | 8 | read `arlen` |
| `snarf_hit_o` | out | 1 | registered hit (one cycle after probe) |
| `snarf_accept_i` | in | 1 | AR admitted as snarf |
| `snarf_rd_valid_o` | out | 1 | snarf data valid |
| `snarf_rd_ready_i` | in | 1 | snarf data ready |
| `snarf_rd_data_o` | out | `AXI_DATA_WIDTH` | snarf data |
| `snarf_rd_last_o` | out | 1 | snarf last beat |

### Oldest entry port

| Signal | Direction | Width | Description |
|---|---|---|---|
| `oldest_valid_o` | out | 1 | oldest valid entry exists |
| `oldest_bank_o` | out | `BKW` | oldest entry bank |
| `oldest_row_o` | out | `ROW_WIDTH` | oldest entry row |
| `oldest_col_o` | out | `COL_WIDTH` | oldest entry column |
| `oldest_id_o` | out | `AXI_ID_WIDTH` | oldest entry ID |
| `oldest_slot_o` | out | `PTRW` | oldest entry slot |

### Scheduler lookup ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `sched_lu_valid_i` | in | `N_SCHED_LU` | per-port valid |
| `sched_lu_bank_i` | in | `N_SCHED_LU*BKW` | per-port bank |
| `sched_lu_row_i` | in | `N_SCHED_LU*ROW_WIDTH` | per-port row |
| `sched_lu_hit_o` | out | `N_SCHED_LU` | per-port hit |
| `sched_lu_slot_o` | out | `N_SCHED_LU*PTRW` | per-port slot |
| `sched_lu_col_o` | out | `N_SCHED_LU*COL_WIDTH` | per-port column |
| `sched_lu_id_o` | out | `N_SCHED_LU*AXI_ID_WIDTH` | per-port ID |
| `sched_lu_age_o` | out | `N_SCHED_LU*AGE_WIDTH` | per-port age |

### Per-entry scheduling vectors

| Signal | Direction | Width | Description |
|---|---|---|---|
| `sch_valid_o` | out | `NUM_ENTRIES` | entry is schedulable |
| `sch_bank_o` | out | `NUM_ENTRIES*BKW` | per-entry bank |
| `sch_row_o` | out | `NUM_ENTRIES*ROW_WIDTH` | per-entry row |
| `sch_col_o` | out | `NUM_ENTRIES*COL_WIDTH` | per-entry column |
| `sch_older_o` | out | `NUM_ENTRIES^2` | flattened age-order matrix |
| `age_thresh_i` | in | 8 | age-threshold boost key |
| `sch_age_exceed_o` | out | `NUM_ENTRIES` | per-entry age-threshold flag |
| `sch_qos_o` | out | `NUM_ENTRIES*4` | per-entry QoS |
| `sch_head_rel_o` | out | `AGE_WIDTH` | relative age of oldest schedulable entry |

### Commit stream

| Signal | Direction | Width | Description |
|---|---|---|---|
| `commit_valid_i` | in | 1 | scheduler commits a slot |
| `commit_ready_o` | out | 1 | commit accepted |
| `commit_slot_i` | in | `PTRW` | slot to commit |
| `cm_rd_valid_o` | out | 1 | commit data valid |
| `cm_rd_ready_i` | in | 1 | commit data ready |
| `cm_rd_data_o` | out | `AXI_DATA_WIDTH` | commit data |
| `cm_rd_strb_o` | out | `AXI_DATA_WIDTH/8` | commit strobe |
| `cm_rd_last_o` | out | 1 | commit last beat |
| `commit_done_valid_o` | out | 1 | B strobe on final sub evict |
| `commit_done_id_o` | out | `AXI_ID_WIDTH` | B ID |

: Table 2.7.2: Write data CAM interface

## Microarchitecture internals

### Entry state

Each CAM entry holds `{valid, bank, row, col, id, qos, age, ptr, pv, fdone, sched, agg, last}`. `ptr` is the SRAM slot, valid after the first fill beat. `fdone` marks fill complete; only then may the entry be scheduled or snarfed. `sched` marks scheduler commit and excludes the entry from further scheduling lookups.

### Age ordering and the matrix

A free-running `r_age_ctr` increments every cycle. Relative age is `w_rel[i] = r_age_ctr - r_age[i]`, which is wrap-safe. The scheduler needs the oldest entry, and the snarf path needs the youngest match.

The original scheduler path computed the oldest by a max-reduce over `w_rel[]`, putting `r_age_ctr` and a chain of `AGE_WIDTH` subtract-compare-mux units directly on the scheduling critical path. On the first post-mode synthesis it measured 63.6 ns against a 15 ns period — pumice ISSUE-005.

The fix is the registered age-order matrix `r_older[i][j]`: bit `[i][j]` is high when entry `i` was inserted before entry `j`. Finding the oldest schedulable entry becomes a shallow `NUM_ENTRIES^2` AND-reduce of 1-bit compares, exposed as `sch_older_o`; only the winner's relative age needs the `AGE_WIDTH` subtract.

```text
// on insert of new slot s:
for every j:
    r_older[s][j] = 0
    if j != s: r_older[j][s] = 1
```

### Snarf lookup

Read-your-write forwarding is limited to the safe case: the write is not yet scheduled (`!r_sched`), the AXI IDs match (same-id W-before-R is the only AXI-ordered case where the read must see the write), and the read's `arlen` equals `AXI_BEATS_PER_BURST-1`.

The probe from `scoria_rd_intake` is registered inside the CAM (`r_sp_*`) before the associative compare, so the cross-module route gets a full cycle and the hit is valid one cycle later. The match is the youngest among valid, filled, unscheduled entries with matching ID, bank, row, and column:

```text
w_sn_match[i] = r_valid[i] && r_fdone[i] && !r_sched[i]
                && (r_id[i]   == r_sp_id)
                && (r_bank[i] == r_sp_bank)
                && (r_row[i]  == r_sp_row)
                && (r_col[i]  == r_sp_col)

is_young[i] = w_sn_match[i] &&
              for all j != i: !(w_sn_match[j] && !r_older[j][i])
snarf_hit_o = r_sp_valid && |is_young && (r_sp_len == AXI_BEATS_PER_BURST-1)
```

### SRAM and shared read port

The data array is one block RAM of `N_SRAM_SLOTS * AXI_BEATS_PER_BURST` words, each packing `{strb, data}`. It has one write port (fill) and one read port shared by snarf and commit; the read is synchronous, registered in `r_rd_q`. A 2-deep prefetch skid FIFO decouples fetch from consume so beat 0 of the next burst prefetches while the current tail drains. Each skid entry carries a full tag (`iscm`, `slot`, `blast`, `agg`, `slast`, `id`) so the consume side never needs the source-FIFO head.

Because there is only one read port, commit has priority and a sustained drain could starve snarf forever. `r_sn_wait` counts cycles a pending snarf is preempted; at `SN_STARVE_LIMIT = 16` snarf wins the port for one fetch, bounding forwarded-read latency without a second read port.

```text
w_sn_starved = (r_sn_wait >= SN_STARVE_LIMIT)
w_sn_fetch = room && sq_valid && (!dq_valid || w_sn_starved)
w_cm_fetch = room && dq_valid && !w_sn_fetch
```

### Rate-matched commit

A write may commit only while fewer than `WR_DRAIN_AHEAD` bursts sit in the drain queue. This prevents the command stream from running far ahead of the data path — with the old "room in the FIFO" gate the command stream could run more than a dozen commands ahead. The arbiter decides a write one cycle before it fires, so `commit_ready_o` answers whether a commit decided now will be accepted next cycle, using `w_dq_occ_next`.

```text
w_commit_fire = commit_valid_i && w_dq_wr_ready
                && (r_dq_occ < WR_DRAIN_AHEAD)
w_dq_occ_next = r_dq_occ + w_commit_fire - w_dq_pop
commit_ready_o = w_dq_wr_ready && (w_dq_occ_next < WR_DRAIN_AHEAD)
```

### Eviction and B consolidation

The CAM entry and its SRAM slot are freed at **fetch-last**, not consume-last. The B strobe and its ID/agg/last tags ride the skid entry, so the response needs no live entry. Fetch-last eviction removes downstream latency from the entry lifetime; with consume-last eviction, eight entries could not sustain a burst every four cycles.

`commit_done_valid_o` fires only on the final sub of a split host burst, consolidating sub-burst responses into one host B:

```text
commit_done_valid_o = w_cm_fire && w_hd_blast && (!w_hd_agg || w_hd_slast)
```

Non-split bursts (`agg=0`) always strobe. Split bursts strobe only when `slast` is high.

## FSM policy

There is no central state machine. State is the entry array, SRAM occupancy, and the fetch-beat pointers; the active stream is the head of the relevant FIFO.

## Timing

Insert is combinational once a free entry and fill-queue slot exist. Snarf hit is registered one cycle after the probe. SRAM read latency is exactly one cycle. The scheduler critical path is now the age-order matrix reduce, a 1-bit operation instead of a wide age subtract chain.

## Notes

- **BRAM read latency trap:** The read latency is exactly one cycle. Do not add an output-register stage or register the read address without deepening the `r_if_*` tag pipeline to match; a mismatch pairs every captured beat with the wrong tag and causes silent data corruption.
- **Why same-ID snarf only:** AXI ordering guarantees W-before-R visibility only within the same ID. Cross-id reads take the DRAM path.
- **WR_DRAIN_AHEAD=2:** Bounds the command-to-data lead to a fixed pipeline latency rather than a FIFO depth.
- **Fetch-last eviction:** Frees the entry and SRAM slot when the last word is fetched, not when the downstream consumer takes it. This is what lets a small CAM cover the write bandwidth.
- **SN_STARVE_LIMIT=16:** A latency bound, not a bandwidth guarantee. A sustained commit stream can still average one snarf fetch every 16 cycles, which is acceptable because snarf is an optimization, not the primary read path.
