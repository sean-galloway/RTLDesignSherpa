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

# Read Command CAM (`scoria_rd_cmd_cam`)

**Module:** `scoria_rd_cmd_cam.sv`
**Location:** `rtl/fub/`
**Category:** scheduling window
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified; formal suite `formal/scoria/rd_cmd_cam/scoria_rd_cmd_cam.sby`

---

## Purpose

The read command CAM is the scheduling window for read sub-commands. It holds up to `NUM_ENTRIES` entries keyed by `{bank, row, col}`, tracks the age order of those entries, and exposes the per-entry vectors the scheduler reads directly. An entry lives only from insert to issue; the return-ring ticket that accompanies a read through DRAM is stored in the entry and forwarded to the return ring on issue.

The CAM deliberately does not hold returned data. Decoupling the scheduling window from the in-flight data buffer is what lets the controller support far more in-flight reads than `NUM_ENTRIES`.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_ENTRIES` | int | 1+ | 8 | CAM scheduling-window entries |
| `N_SCHED_LU` | int | 1+ | 4 | generic scheduler lookup ports |
| `NUM_BANKS` | int | 1+ | 8 | DRAM banks |
| `ROW_WIDTH` | int | 1+ | 14 | row address width |
| `COL_WIDTH` | int | 1+ | 10 | column address width |
| `AXI_ID_WIDTH` | int | 1+ | 8 | AXI ID width |
| `AGE_WIDTH` | int | 1+ | 16 | free-running age-counter width |
| `RD_RET_DEPTH` | int | power of 2 | 32 | return-ring depth; bounds ticket space |

: Table 2.9.1: Read command CAM parameters

## Interface

### Insert

| Signal | Direction | Width | Description |
|---|---|---|---|
| `ins_valid_i` | in | 1 | allocate a CAM entry |
| `ins_ready_o` | out | 1 | a free slot exists |
| `ins_bank_i` | in | `$clog2(NUM_BANKS)` | decoded bank |
| `ins_row_i` | in | `ROW_WIDTH` | decoded row |
| `ins_col_i` | in | `COL_WIDTH` | decoded column |
| `ins_id_i` | in | `AXI_ID_WIDTH` | AXI ID |
| `ins_qos_i` | in | 4 | AxQOS |
| `ins_ticket_i` | in | `$clog2(RD_RET_DEPTH)` | return-ring ticket from `scoria_rd_return_ring` |

: Table 2.9.2: Insert interface

### Scheduler vectors

| Signal | Direction | Width | Description |
|---|---|---|---|
| `sch_valid_o` | out | `NUM_ENTRIES` | per-entry valid |
| `sch_bank_o` | out | `NUM_ENTRIES * bank_width` | per-entry bank |
| `sch_row_o` | out | `NUM_ENTRIES * ROW_WIDTH` | per-entry row |
| `sch_col_o` | out | `NUM_ENTRIES * COL_WIDTH` | per-entry column |
| `sch_older_o` | out | `NUM_ENTRIES²` | flattened age-order matrix |
| `age_thresh_i` | in | 8 | age-threshold boost key |
| `sch_age_exceed_o` | out | `NUM_ENTRIES` | per-entry age-exceed flag |
| `sch_qos_o` | out | `NUM_ENTRIES * 4` | per-entry AxQOS |
| `sch_head_rel_o` | out | `AGE_WIDTH` | relative age of oldest schedulable entry |

: Table 2.9.3: Flat per-entry scheduler vectors

### Generic scheduler lookup ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `sched_lu_valid_i` | in | `N_SCHED_LU` | lookup valid |
| `sched_lu_bank_i` | in | `N_SCHED_LU * bank_width` | lookup bank |
| `sched_lu_row_i` | in | `N_SCHED_LU * ROW_WIDTH` | lookup row |
| `sched_lu_hit_o` | out | `N_SCHED_LU` | lookup hit |
| `sched_lu_slot_o` | out | `N_SCHED_LU * $clog2(NUM_ENTRIES)` | hit slot |
| `sched_lu_col_o` | out | `N_SCHED_LU * COL_WIDTH` | hit column |
| `sched_lu_id_o` | out | `N_SCHED_LU * AXI_ID_WIDTH` | hit ID |
| `sched_lu_age_o` | out | `N_SCHED_LU * AGE_WIDTH` | hit relative age |

: Table 2.9.4: Generic scheduler lookup ports

### Oldest fallback port

| Signal | Direction | Width | Description |
|---|---|---|---|
| `oldest_valid_o` | out | 1 | an entry exists |
| `oldest_bank_o` | out | bank width | bank of oldest entry |
| `oldest_row_o` | out | `ROW_WIDTH` | row of oldest entry |
| `oldest_col_o` | out | `COL_WIDTH` | column of oldest entry |
| `oldest_id_o` | out | `AXI_ID_WIDTH` | ID of oldest entry |
| `oldest_slot_o` | out | `$clog2(NUM_ENTRIES)` | slot of oldest entry |

: Table 2.9.5: Oldest fallback port

### Issue notify

| Signal | Direction | Width | Description |
|---|---|---|---|
| `issue_valid_i` | in | 1 | scheduler issued this slot |
| `issue_ready_o` | out | 1 | ring's issue-order FIFO ready |
| `issue_slot_i` | in | `$clog2(NUM_ENTRIES)` | issued slot |
| `iss_valid_o` | out | 1 | ticket forward valid |
| `iss_ready_i` | in | 1 | ring's issue-order FIFO ready |
| `iss_ticket_o` | out | `$clog2(RD_RET_DEPTH)` | ticket forwarded to return ring |
| `busy_o` | out | 1 | any entry valid |

: Table 2.9.6: Issue notify interface

## Microarchitecture internals

### Entry fields

Each CAM entry stores:

```text
{valid, bank, row, col, id, qos, ticket, age}
```

The ticket is the return-ring slot allocated when the read was admitted. It stays with the entry from insert until issue, at which point it is forwarded to the return ring's issue-order FIFO. The CAM entry is freed on the issue cycle; the read's data return is owned entirely by the return ring from that point on.

### Ticket carried from insert to issue

`scoria_axi4_layer` allocates a return-ring ticket at the same time it inserts a CAM entry. The ticket is presented on `ins_ticket_i` and latched into `r_ticket[slot]`. On a valid issue fire (`w_issue_fire`), the ticket is driven onto `iss_ticket_o` with `iss_valid_o` high. The issue-ready handshake comes from the return ring's issue-order FIFO, so the CAM cannot issue faster than the ring can accept tickets.

### Age-order matrix

Relative age is `w_rel[i] = r_age_ctr - r_age[i]`. The CAM does not expose a wide age key to the scheduler. Instead it maintains a registered `r_older[i][j]` matrix where bit `r_older[i][j]` means entry `i` is older than entry `j`. The matrix is updated only on insert: the new slot is youngest, so it is older than nobody, and every existing slot becomes older than it.

### Oldest via 1-bit AND-reduce

The scheduler-side oldest entry is found with a 1-bit AND-reduce over the matrix. For each slot `i`:

```text
w_sho_is[i] = r_valid[i] AND (for all j != i: r_valid[j] -> r_older[i][j])
```

The winner is the highest-numbered slot whose `w_sho_is` is true. Only the winner's relative age needs the `AGE_WIDTH` subtract, which is how the matrix replaced the original wide age-compare path (pumice ISSUE-005).

### `sch_age_exceed_o` versus `age_thresh_i`

`age_thresh_i` is a runtime CSR from the scheduler. The per-entry flag is registered:

```text
r_age_exceed[i] = r_valid[i] && (age_thresh_i != 0) && (w_rel[i] >= {age_thresh_i, 4'h0})
```

The flag is one cycle stale, which is acceptable because the age-threshold order mode uses it as a preference key, not as a safety guard. `sch_age_exceed_o[i] = r_valid[i] && r_age_exceed[i]`.

### Unused ports tied off in scoria

The generic `sched_lu_*` lookup ports and the `oldest_*` fallback port are not used by `scoria_cmd_arbiter`. The scheduler reads the flat per-entry vectors directly so it can activate banks in parallel without a lookup round-trip. In `scoria_axi4_layer` the lookup inputs are tied to zero and the outputs are left unconnected.

## FSM policy

There is no state machine. The CAM is a set of registers, comparators, and priority encoders. Insert allocation picks the highest-numbered free slot; issue frees the selected slot and forwards its ticket.

## Timing

Insert is combinational from `ins_valid_i` to `ins_ready_o`. The scheduler vectors are registered fields with one level of derive. Issue is combinational from `issue_valid_i` to `iss_valid_o`, qualified by `issue_ready_o` from the return ring.

## Notes

- **Input-contract assertion at `scoria_rd_cmd_cam.sv:321-322`:** a non-synthesis assertion fires if the scheduler issues a slot that is not valid. This is an input contract on the issuer, not a property of the CAM. It is mirrored here because the block historically had no dedicated DV suite. The same contract is stated as an assumption in `formal/scoria/rd_cmd_cam/formal_scoria_rd_cmd_cam.sv`, so the formal proof takes it as given.
- **Formal coverage now exists:** the block has a dedicated `scoria_rd_cmd_cam.sby` suite. The simulation assertion remains as an independent cross-check and is guarded from synthesis.
- **CAM depth is not the in-flight limit:** `NUM_ENTRIES` is only the scheduling window. The number of reads the controller can hold in flight is bounded by `scoria_rd_return_ring.DEPTH`, not by this CAM.
