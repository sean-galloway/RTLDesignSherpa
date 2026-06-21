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

# Write Command CAM (`wr_cmd_cam`)

**Module:** `wr_cmd_cam.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent:** `ddr2_lpddr2_ctrl`
**Status:** Skeleton

---

## Purpose

`wr_cmd_cam` is the **write-side content-addressable storage** of in-flight write commands. It mirrors the read CAM's role for write traffic but carries different per-slot metadata:

- Pointer into the AXI-side write-data buffer (`w_buf_ptr`)
- Pointer into the AXI-side write-strobe buffer (`strb_ptr`)
- Per-slot beats-issued counter (so the FUB knows when the last W beat has been pushed to DFI write data)

Separation from the read CAM lets the write path sit shallow — writes complete on B response, which is a single AXI event, so the write CAM does not need to track per-beat return.

## Parameters

| Parameter            | Default | Purpose                              |
|----------------------|---------|--------------------------------------|
| `WR_CAM_DEPTH`       | 16      | Number of in-flight write slots      |
| `IDW`                | `AXI_ID_WIDTH` | Key width                       |
| `W_BUF_PTR_WIDTH`    | `$clog2(W_BUF_DEPTH)` | Pointer into AXI W buffer |
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
| `burst_len`      | `BURST_LEN_WIDTH`     | Total beats                                          |
| `beats_issued`   | `BURST_LEN_WIDTH`     | Beats already pushed to DFI write data               |
| `w_buf_ptr`      | `W_BUF_PTR_WIDTH`     | Pointer into the AXI W-buffer for next beat          |
| `strb_ptr`       | `W_BUF_PTR_WIDTH`     | Pointer into the per-beat strobe buffer              |
| `issued`         | 1                     | Scheduler has picked this entry                      |
| `b_pending`      | 1                     | Awaiting B response from DFI write completion        |

Total per-slot width: ~58 bits in the default config. Total storage (16 × 58): ~116 bytes, distributed flops.

## Interfaces

### Push (from `axi4_slave_fub`)

Same shape as the read CAM push, plus `w_buf_ptr` and `strb_ptr` (which the AXI slave allocates at push time).

### Scheduler Query

Same shape as the read CAM. The scheduler matches by (rank, bank) and selects with row-hit priority.

### Issue Notification

When the scheduler picks a write, the CAM:
1. Marks `issued = 1`
2. Begins handing per-beat data to `wr_data_path_fub` via the `beat_data_pull` interface (below)

### Beat-Pull (to `wr_data_path_fub`)

| Signal             | Direction | Description                                |
|--------------------|-----------|--------------------------------------------|
| `beat_pull_o`      | output    | Strobe — pull next beat for this slot      |
| `beat_pull_slot_o` | output    | Slot index whose beat is being pulled      |
| `beat_pull_ptr_o`  | output    | `w_buf_ptr + beats_issued`                 |
| `beat_pull_strb_o` | output    | `strb_ptr + beats_issued`                  |
| `beat_pull_last_o` | output    | 1 when this is the burst's final beat       |

`wr_data_path_fub` walks the AXI W buffer at the supplied pointer and pushes to DFI wrdata. On the last beat, it asserts `b_pending_set` to the CAM.

### Completion (from DFI write window expiration)

| Signal              | Direction | Description                                 |
|---------------------|-----------|---------------------------------------------|
| `b_pending_set_i`   | input     | Last W beat pushed; await tCWL+tWR window   |
| `b_complete_i`      | input     | Write window expired (from `xbank_timers`)  |
| `entry_complete_o`  | output    | Burst is fully complete; signal `axi4_slave_fub` to push B response |

## Difference From Read CAM

| Aspect              | Read CAM                                     | Write CAM                                          |
|---------------------|----------------------------------------------|----------------------------------------------------|
| Lifecycle           | Push → issue → beats return → clear           | Push → issue → beats issued → write window expires → B → clear |
| Beat tracking       | Counts beats *returned* from DFI               | Counts beats *issued* to DFI; also tracks the post-issue write window |
| AXI ID echo         | `rid` returned with each R beat                | `bid` returned once at B-response time              |
| Pointer fields      | none (just a beat counter)                     | `w_buf_ptr`, `strb_ptr` into AXI-side buffers       |
| Completion driver   | `rd_data_path` (last beat of R)                | `xbank_timers` (write window expiration) → `wr_data_path` |

The asymmetry justifies the separate FUBs. Trying to share a CAM would either inflate the read slot to carry write-only fields, or vice versa.

## Timing Budget

Same shape as the read CAM. The combinational match-line path is shared with `rd_cmd_cam` in the scheduler's match aggregation.

## CSR Hooks

- `STATUS.wr_cam_occ` — current occupancy
- `STATUS.wr_b_pending` — count of slots awaiting B response
- `OBS_WR_CAM_HIGH_WATER` — peak occupancy

## TODO

- Mermaid for the issued → beat-pull → b_pending → b_complete lifecycle
- Wavedrom showing a multi-beat write burst from CAM push to B response
- Backpressure path when `wr_data_path` can't keep up with `beat_pull` (rare; DFI wrdata is wider than AXI W)
