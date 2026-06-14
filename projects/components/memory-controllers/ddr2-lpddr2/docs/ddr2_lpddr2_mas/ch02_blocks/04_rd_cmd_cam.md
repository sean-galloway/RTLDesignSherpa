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

# Read Command CAM (`rd_cmd_cam_fub`)

**Module:** `rd_cmd_cam_fub.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent:** `ddr2_lpddr2_ctrl`
**Status:** Skeleton

---

## Purpose

`rd_cmd_cam_fub` is the **read-side content-addressable storage** of in-flight read commands. It holds the DRAM-layer view (rank, bank, row, col) of every read burst that has been pushed by `axi4_slave_fub` and not yet fully returned on the AXI R-channel.

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

The scheduler queries the CAM to:
- Find all unissued entries matching a target (rank, bank) — for next-issue selection
- Find row-hit candidates (entries whose row == open_row[rank][bank])

| Signal              | Direction | Description                                                  |
|---------------------|-----------|--------------------------------------------------------------|
| `q_rank_i`          | input     | Query rank                                                   |
| `q_bank_i`          | input     | Query bank                                                   |
| `q_row_i`           | input     | Query row (for row-hit check)                                |
| `match_unissued_o`  | output    | One-hot vector of slots matching (rank, bank) and not issued |
| `match_rowhit_o`    | output    | One-hot vector of slots matching (rank, bank, row) and not issued |
| `match_data_o`      | output    | The selected slot's payload (rank, bank, row, col, len)      |

### Issue Notification

When the scheduler picks an entry from this CAM:

| Signal           | Direction | Description                                |
|------------------|-----------|--------------------------------------------|
| `issued_slot_i`  | input     | Slot index to mark as issued               |
| `issued_we_i`    | input     | Mark-issued strobe                         |

### Beat Return (from `rd_data_path_fub`)

| Signal           | Direction | Description                                |
|------------------|-----------|--------------------------------------------|
| `beat_id_i`      | input     | AXI ID of returning beat                   |
| `beat_we_i`      | input     | Beat-arrived strobe                        |
| `entry_complete_o` | output  | One-hot vector of slots that just completed (last beat of their burst) |

On entry-complete the slot's `valid` is cleared in the next cycle.

## Lookup Mechanism

The CAM uses a **parallel match-line** structure: each slot has a small comparator for {rank, bank} that drives a per-slot match wire. The scheduler reads the full match-vector and picks among matches using a priority encoder (age-priority — oldest slot wins ties).

For the typical RD_CAM_DEPTH of 16 with `BA=3`, `$clog2(NR)=1..2` (1 for single-rank, 2 for quad-rank), this is 16 4–5-bit equality comparators in parallel — trivial silicon.

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

The combinational match path is on the scheduler's critical loop and is shared with `wr_cmd_cam_fub` and the bank machines' state matrix. See `ch02_blocks/07_scheduler.md` for the full critical-path breakdown.

## CSR Hooks

- `STATUS.rd_cam_occ` — current occupancy
- `OBS_RD_CAM_HIGH_WATER` — peak occupancy observed since last read

## TODO

- Mermaid for the parallel match-line topology
- Wavedrom: push → scheduler-match → issue → beats return → clear
- Per-ID head-of-queue ordering corner case spec
