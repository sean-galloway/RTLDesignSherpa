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

# Read Command CAM (`rd_cmd_cam`)

**Module:** `rd_cmd_cam.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent:** `ddr2_lpddr2_ctrl`
**Status:** Skeleton

---

## Purpose

`rd_cmd_cam` is the **read-side content-addressable storage** of in-flight read commands. It holds the DRAM-layer view (rank, bank, row, col) of every read burst that has been pushed by `axi4_slave_fub` and not yet fully returned on the AXI R-channel.

The CAM is keyed by **AXI ID**, allowing the scheduler to find all reads to a given (rank, bank) without iterating the queue and allowing `rd_data_path_fub` to find the right entry to decrement when a read beat returns.

The read CAM and write CAM are intentionally separate FUBs — see §1.1 for the rationale.

## Parameters

| Parameter            | Default | Purpose                              |
|----------------------|---------|--------------------------------------|
| `RD_CAM_DEPTH`       | 16      | Number of in-flight read slots       |
| `IDW`                | `AXI_ID_WIDTH` | Key width                       |
| `BURST_LEN_WIDTH`    | 8       | Burst-length field width             |

## Storage Per Slot

| Field            | Width                 | Description                                          |
|------------------|-----------------------|------------------------------------------------------|
| `valid`          | 1                     | Slot occupied                                        |
| `axi_id`         | `IDW`                 | Key — the originating AXI ID                         |
| `rank`           | `$clog2(NR)`          | Decoded rank                                         |
| `bank`           | `BA`                  | Decoded bank                                         |
| `row`            | `ROW_WIDTH`           | Decoded row                                          |
| `col_start`      | `COL_WIDTH`           | Starting column                                      |
| `burst_len`      | `BURST_LEN_WIDTH`     | Total beats in burst                                 |
| `beats_returned` | `BURST_LEN_WIDTH`     | Beats already returned on R                          |
| `issued`         | 1                     | Scheduler has picked this entry                      |
| `last_beat_at`   | small                 | Cycle of last beat return (for latency telemetry)    |

Total per-slot width (default config): ~46 bits.

Total storage (16 entries × 46 b): ~92 bytes — small enough to fit comfortably in distributed flops with no SRAM macro.

## Interfaces

### Push (from `axi4_slave_fub`)

| Signal       | Direction | Width             | Description                                |
|--------------|-----------|-------------------|--------------------------------------------|
| `push_valid` | input     | 1                 | New read burst arriving                    |
| `push_ready` | output    | 1                 | CAM has a free slot                        |
| `push_id`    | input     | `IDW`             | AXI ID                                     |
| `push_rank`  | input     | `$clog2(NR)`      | from `addr_mapper`                         |
| `push_bank`  | input     | `BA`              |                                            |
| `push_row`   | input     | `ROW_WIDTH`       |                                            |
| `push_col`   | input     | `COL_WIDTH`       |                                            |
| `push_len`   | input     | `BURST_LEN_WIDTH` |                                            |

### Scheduler Query

The scheduler scans the full match vector across **all** slots and picks
by AXI QoS (highest wins; lowest-slot-index breaks ties). It does NOT
drive `q_rank_i` / `q_bank_i` / `q_row_i` in the v1 revision — those
ports are tied to 0 inside `scheduler.sv`. The CAM therefore exposes
two distinct match vectors with two distinct contracts:

| Signal              | Direction | Description                                                                              |
|---------------------|-----------|------------------------------------------------------------------------------------------|
| `q_rank_i`          | input     | Query rank (not driven by scheduler in v1)                                               |
| `q_bank_i`          | input     | Query bank (not driven by scheduler in v1)                                               |
| `q_row_i`           | input     | Query row (not driven by scheduler in v1)                                                |
| `match_pending_o`   | output    | One-hot vector of slots that are valid and not issued. **Independent of `q_*`.** The scheduler's slot-picker scans this; gating on the q_* ports here would silently hide every non-`q_*` slot from the picker. |
| `match_rowhit_o`    | output    | Subset of `match_pending_o` further restricted to slots whose `(rank, bank, row)` equals `(q_rank_i, q_bank_i, q_row_i)`. The scheduler does not yet consume this — reserved for a future row-hit-first picker. |

**Snapshot interface.** The scheduler reads the picked slot's payload
(rank, bank, row, col, len, qos, id) directly from per-slot snapshot
output ports (`snap_rank_o`, `snap_bank_o`, …, `snap_id_o`) instead of
a single muxed `match_data_o`. This avoids re-driving the query bus
once the picker has selected a slot.

> **Implementation note — match_pending contract.** The `valid & !issued`
> contract on `match_pending_o` is load-bearing: the scheduler picks
> across **all** valid+unissued slots regardless of bank. A pre-v1 mistake
> gated `match_pending_o` on `(r_bank == q_bank_i) && (r_rank == q_rank_i)`
> with `q_*` tied to 0, which collapsed all reads onto bank 0 — every
> AXI read to bank 1-7 sat in the CAM forever. Pinned at FUB level by
> `test_rd_cmd_cam[match_pending_scheduler_contract]`.

### Issue Notification

When the scheduler picks an entry from this CAM:

| Signal           | Direction | Description                                |
|------------------|-----------|--------------------------------------------|
| `issued_slot_i`  | input     | Slot index to mark as issued               |
| `issued_we_i`    | input     | Mark-issued strobe                         |

### Beat Return (from `rd_data_path_fub`)

The retire interface is keyed by **slot index**, not AXI ID. The
slot→ID mapping is exposed separately on `snap_id_o` (see the snapshot
interface) so `rd_cl_aligner` can stamp the right `rd_inject_id_o` on
each returned beat.

| Signal           | Direction | Description                                                            |
|------------------|-----------|------------------------------------------------------------------------|
| `beat_slot_i`    | input     | Slot index of returning beat                                           |
| `beat_we_i`      | input     | Beat-arrived strobe                                                    |
| `entry_complete_o` | output  | High in the same cycle the last beat retires                            |
| `entry_complete_slot_o` | output | Slot index that just completed                                     |
| `entry_complete_id_o` | output | AXI ID of the completed entry — feeds the AXI R-channel's `rid` echo |

On entry-complete the slot's `valid` is cleared in the next cycle.

> **Implementation note — `snap_id_o` must flow.** The `snap_id_o`
> port is what carries the AR's AXI ID up to `ddr2_lpddr2_top.sv` so
> the core's `rd_op_id` lookup (indexed by `cmd_rd_slot`) can stamp
> `rd_cl_aligner`'s `op_id_i`, which becomes `rd_inject_id_o` on each
> beat. If `snap_id_o` is dropped at the macro boundary or the top
> ties `rd_snap_id` to `'0`, every read response is stamped with
> `id=0` and any multi-ID OOO workload silently mis-routes its R
> beats. Pinned at FUB level by `test_rd_cl_aligner[id_propagate]`'s
> `verify_capture` assertion that `rd_inject_id_o == op_id_i` for
> every beat.

## Lookup Mechanism

The CAM exposes two parallel match-line structures:

  * `match_pending_o[i]` is a 1-bit per slot equal to `r_valid[i] &&
    !r_issued[i]`. No comparator — this is the broad "needs servicing"
    vector the scheduler consumes.
  * `match_rowhit_o[i]` adds three equality comparators on
    `(rank, bank, row)` against the `q_*` query bus. Reserved for a
    future row-hit-first picker; not driven by the scheduler in v1.

For the typical RD_CAM_DEPTH of 16 with `BA=3` and `$clog2(NR)=1..2`,
`match_rowhit_o` is 16 18-19-bit equality comparators in parallel —
still trivial silicon.

The scheduler's slot-picker iterates over `match_pending_o`, picking
the slot with the highest AXI QoS (ties go to the lowest slot index —
oldest under the free-slot priority encoder).

## Per-ID Beat Counting

Because reads return in-order *per AXI ID* (an AXI ordering rule), the read CAM does not need a per-beat slot table. A slot's `beats_returned` increments on each beat that returns with that ID, and when `beats_returned == burst_len` the slot completes and clears.

If `AXI_OOO_ACROSS_IDS == false` (rare), the SoC has asked for in-order return across all IDs, and the read CAM enforces this by issuing a head-of-queue priority hint to the scheduler — entries are still cleared in arrival order. The OoO-across-IDs default is `true`; per-ID in-order is the AXI default and is preserved.

## Timing Budget

| Path                                  | Budget       |
|---------------------------------------|--------------|
| `push_valid` → slot occupy (1 cycle)  | 1 cycle      |
| `q_rank_i / q_bank_i` → `match_*_o`   | combinational |
| `beat_id_i` → `beats_returned[slot]+1` | 1 cycle     |
| `entry_complete_o` → slot clear        | 1 cycle     |

The combinational match path is on the scheduler's critical loop and is shared with `wr_cmd_cam` and the bank machines' state matrix. See `ch02_blocks/07_scheduler.md` for the full critical-path breakdown.

## CSR Hooks

- `STATUS.rd_cam_occ` — current occupancy
- `OBS_RD_CAM_HIGH_WATER` — peak occupancy observed since last read

## TODO

- Mermaid for the parallel match-line topology
- Wavedrom: push → scheduler-match → issue → beats return → clear
- Per-ID head-of-queue ordering corner case spec
