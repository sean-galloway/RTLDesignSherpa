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

# AXI4 Layer (`scoria_axi4_layer`)

**Module:** `scoria_axi4_layer.sv` / **Location:** `rtl/macro/` / **Category:** host interface / **Parent:** `scoria_core` / **Status:** complete and sim-verified.

---

## Purpose

The AXI4 layer is the host-facing front end. It takes the full AXI4 slave interface, chops each burst into DFI-burst-sized sub-commands, maps each sub-command to `{rank, bank, row, col}`, buffers write data in the write-data CAM, and holds the read-command CAM plus the read-return ring. It exposes the scheduling window as flat per-entry vectors so the scheduler can pick bank-parallel commands without a CAM lookup round-trip.

The block is structural: no FSM, no storage of its own beyond the instantiated CAMs and FIFOs. Its RTL is inherited unchanged from pumice (verified by `test_scoria_pumice_logic_parity.py`).

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `AXI_ID_WIDTH` | int | 8 | Host AXI ID width |
| `AXI_ADDR_WIDTH` | int | 32 | Host address width |
| `AXI_DATA_WIDTH` | int | 64 | Host data width; also the DFI word width here |
| `AXI_USER_WIDTH` | int | 1 | AXI USER width |
| `DRAM_BEAT_WIDTH` | int | 64 | Misnomer; passed as the AXI width to size `DRAM_BURST_BYTES` only |
| `NUM_RANKS` | int | 1 | DRAM ranks |
| `NUM_BANKS` | int | 8 | DRAM banks |
| `ROW_WIDTH` | int | 14 | Row address width |
| `COL_WIDTH` | int | 10 | Column address width |
| `BYTE_OFFSET_WIDTH` | int | 3 | log2(device word bytes) |
| `AXI_BEATS_PER_BURST` | int | 4 | AXI beats per DFI burst / per sub-command |
| `NUM_ENTRIES` | int | 8 | CAM scheduling-window entries |
| `N_SRAM_SLOTS` | int | `NUM_ENTRIES` | Write-data SRAM slots |
| `N_SCHED_LU` | int | 4 | Scheduler lookup ports (unused in scoria) |
| `AGE_WIDTH` | int | 16 | Free-running age-counter width |
| `RD_RET_DEPTH` | int | 32 | In-flight read capacity; power of 2 |

: Table 2.1.1: AXI4 layer parameters

`AXI_DATA_WIDTH` is the DFI word width because `scoria_core` instantiates the macro with `DRAM_BEAT_WIDTH` set to the AXI width. The front end is DFI-word granular: one AXI beat equals one DFI word.

## Interface

### Host AXI4 ports

The layer presents a full AXI4 slave. All `s_axi_*` names follow the AXI4 spec; standard signals are grouped by channel below.

| Group | Signals | Width notes |
|---|---|---|
| Write address | `s_axi_awid/addr/len/size/burst/lock/cache/prot/qos/region/user/valid` | `AW`, `IW`, 8, 3, 2, 1, 4, 3, 4, 4, `UW` |
| Write address handshake | `s_axi_awready` | 1 |
| Write data | `s_axi_wdata/wstrb/wlast/wuser/wvalid` | `DW`, `DW/8`, 1, `UW` |
| Write data handshake | `s_axi_wready` | 1 |
| Write response | `s_axi_bid/bresp/buser/bvalid` | `IW`, 2, `UW` |
| Write response handshake | `s_axi_bready` | 1 |
| Read address | `s_axi_arid/addr/len/size/burst/lock/cache/prot/qos/region/user/valid` | `AW`, `IW`, 8, 3, 2, 1, 4, 3, 4, 4, `UW` |
| Read address handshake | `s_axi_arready` | 1 |
| Read data | `s_axi_rid/rdata/rresp/rlast/ruser/rvalid` | `IW`, `DW`, 2, 1, `UW` |
| Read data handshake | `s_axi_rready` | 1 |

: Table 2.1.2: Host AXI4 interface

### Address-mapping CSR ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `bank_lsb_i` | in | 5 | `ADDR_MAP.bank_lsb`: bit index of bank in decoded address |
| `hash_en_i` | in | 1 | `ADDR_MAP.hash_en`: enable bank hashing |
| `hash_seed_i` | in | 8 | `ADDR_MAP.hash_seed`: hashing seed |

: Table 2.1.3: Address-mapping configuration ports

### Write scheduler and commit-data ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wr_sch_valid_o` | out | `NUM_ENTRIES` | Per-entry valid bits |
| `wr_sch_bank_o` | out | `NUM_ENTRIES * BKW` | Per-entry bank |
| `wr_sch_row_o` | out | `NUM_ENTRIES * ROW_WIDTH` | Per-entry row |
| `wr_sch_col_o` | out | `NUM_ENTRIES * COL_WIDTH` | Per-entry column |
| `wr_sch_older_o` | out | `NUM_ENTRIES^2` | Flattened age-order matrix |
| `wr_sch_age_exceed_o` | out | `NUM_ENTRIES` | Entry age exceeds threshold |
| `wr_sch_qos_o` | out | `NUM_ENTRIES * 4` | Per-entry AXI QoS |
| `wr_sch_head_rel_o` | out | 16 | Relative age of head entry |
| `wr_commit_valid_i` | in | 1 | Scheduler commits a write entry |
| `wr_commit_ready_o` | out | 1 | Write CAM can accept the commit |
| `wr_commit_slot_i` | in | `PTRW` | Slot to commit |
| `wr_cm_rd_valid_o` | out | 1 | Commit-data stream valid |
| `wr_cm_rd_ready_i` | in | 1 | Commit-data stream ready |
| `wr_cm_rd_data_o` | out | `AXI_DATA_WIDTH` | Commit data |
| `wr_cm_rd_strb_o` | out | `AXI_DATA_WIDTH/8` | Commit strobe |
| `wr_cm_rd_last_o` | out | 1 | Final beat of the committed burst |

: Table 2.1.4: Write scheduler and commit-data ports

### Read scheduler and DFI return ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `rd_sch_valid_o` | out | `NUM_ENTRIES` | Per-entry valid bits |
| `rd_sch_bank_o` | out | `NUM_ENTRIES * BKW` | Per-entry bank |
| `rd_sch_row_o` | out | `NUM_ENTRIES * ROW_WIDTH` | Per-entry row |
| `rd_sch_col_o` | out | `NUM_ENTRIES * COL_WIDTH` | Per-entry column |
| `rd_sch_older_o` | out | `NUM_ENTRIES^2` | Flattened age-order matrix |
| `rd_sch_age_exceed_o` | out | `NUM_ENTRIES` | Entry age exceeds threshold |
| `rd_sch_qos_o` | out | `NUM_ENTRIES * 4` | Per-entry AXI QoS |
| `rd_sch_head_rel_o` | out | 16 | Relative age of head entry |
| `sched_age_thresh_i` | in | 8 | Age-threshold key for both CAMs |
| `rd_issue_valid_i` | in | 1 | Scheduler issues a read entry |
| `rd_issue_ready_o` | out | 1 | Read CAM can accept the issue |
| `rd_issue_slot_i` | in | `PTRW` | Slot to issue |
| `rd_dfi_ret_valid_i` | in | 1 | DFI read return valid |
| `rd_dfi_ret_ready_o` | out | 1 | Read-return ring can accept return |
| `rd_dfi_ret_data_i` | in | `AXI_DATA_WIDTH` | Return data |
| `rd_dfi_ret_resp_i` | in | 2 | Return response |
| `rd_dfi_ret_last_i` | in | 1 | Return last beat |

: Table 2.1.5: Read scheduler and DFI return ports

### Status port

| Signal | Direction | Width | Description |
|---|---|---|---|
| `busy_o` | out | 1 | OR of sub-module busy flags |

: Table 2.1.6: Status port

## Microarchitecture internals

### Instantiation tree

The layer instantiates seven sub-blocks:

- `scoria_wr_splitter` — chops AW into DFI-burst sub-commands and reframes W.
- `scoria_wr_intake` — skid buffers, decoded push to the write CAM.
- `scoria_wr_data_cam` — write scheduling window and data SRAM.
- `scoria_axi_burst_chopper` — chops AR into DFI-burst sub-commands.
- `scoria_rd_intake` — read snarf probe, decoded miss push, return reorder.
- `scoria_rd_cmd_cam` — read scheduling window.
- `scoria_rd_return_ring` — AR-order in-flight read buffer.

### Write datapath

Host write bursts enter through `scoria_wr_splitter`. The splitter uses `scoria_axi_burst_chopper` with `PAD_TO_CHUNK = 1` so every sub-command is declared as a full `AXI_BEATS_PER_BURST` beats. It regenerates `WLAST` every `AXI_BEATS_PER_BURST` beats and pads short host bursts with zero-strobe beats, holding `fub_wready` low during padding.

The split stream reaches `scoria_wr_intake`, which skid-buffers AXI, maps the head address to `{rank, bank, row, col}`, and pushes the decoded command into `scoria_wr_data_cam`. The intake buffers write data and pops it in CAM commit order.

`scoria_wr_data_cam` allocates one entry and one SRAM slot per sub-command. As W beats arrive they fill the SRAM. The scheduler reads the flat `wr_sch_*` vectors, commits an entry with `wr_commit_valid_i`/`wr_commit_slot_i`, and the CAM streams the committed burst data out on `wr_cm_rd_*`. On the final sub-command's last beat the CAM asserts `commit_done_valid_o` plus the stored ID so the intake can generate the host B response.

### Read datapath

Host read bursts enter through `scoria_axi_burst_chopper` with `PAD_TO_CHUNK = 0`. Each sub-command carries `m_ax_agg` and `m_ax_last`; the read intake uses `last` to collapse `RLAST` and drops beats beyond the requested `AxLEN`.

`scoria_rd_intake` skid-buffers AR, probes `scoria_wr_data_cam` for a same-ID snarf hit, and admits misses to `scoria_rd_cmd_cam`. A two-stage admit pipeline lets the head AR stay probed while the previous AR is pushed, so admits can occur every cycle. Snarf hits stream directly from the CAM SRAM; misses go through the read CAM and return ring.

### Read-after-write snarf

The snarf probe is registered: `scoria_rd_intake` presents `{bank, row, col, id, len}` to `scoria_wr_data_cam` and receives `snarf_hit_o` one cycle later. A hit is accepted only if it matches the youngest valid, fully-written, not-yet-scheduled entry with the same ID and burst length. The read intake's order FIFO tags snarf-sourced reads with `SRC_SNARF` so they merge correctly with DFI-sourced returns in AR order. Snarf is same-ID only.

### Read-command CAM and return-ring cooperation

A read is admitted only when both the read CAM and the return ring have room:

```text
ar_push_ready = rd_cam_ins_ready && rt_alloc_ready
```

The ring allocates a ticket in strict AR order. The ticket rides into the `scoria_rd_cmd_cam` entry at insert and is forwarded back out on `rd_issue_valid_i`. Once the read issues to DRAM, the CAM entry frees but the ticket follows the data through the return ring. The ring depth, not the CAM depth, bounds how many reads can be in flight.

### Flat scheduler vectors and legacy port tie-offs

Both CAMs expose per-entry scheduler vectors (`sch_valid`, `sch_bank`, `sch_row`, `sch_col`, `sch_older`, `sch_age_exceed`, `sch_qos`, `sch_head_rel`) so the arbiter can do bank-parallel classification without a CAM lookup. The generic `sched_lu_*` and `oldest_*` ports are intentionally tied off: `sched_lu_valid_i` is driven to `'0` and the `oldest_*` outputs are left open. Synthesis prunes them.

## FSM policy

There is no FSM in this layer. Burst chopping is combinational plus a single `r_active` bit in the chopper. CAM allocation, fill, and drain are governed by the CAM internal state, not by a layer-level controller.

## Timing

All logic is in the `aclk` controller clock domain. The AXI splitter and chopper accept the first sub-command combinationally and hold `ready` low until the burst drains. The CAMs add one cycle of registered snarf-hit latency and one cycle of synchronous-read BRAM latency on commit-data and snarf-data returns.

## Notes

- `DRAM_BEAT_WIDTH` is a misnomer in this layer. `scoria_core` instantiates the macro with `.DRAM_BEAT_WIDTH(DW)` where `DW` is the AXI data width, not the true DRAM beat width. The parameter survives only to size `DRAM_BURST_BYTES`.
- `AXI_DATA_WIDTH` equals the DFI word width because the front end is DFI-word granular.
- `AXI_BEATS_PER_BURST` is the sub-command granularity, not the JEDEC burst length. The same identifier has been used for three different quantities in the design.
- `scoria_axi4_layer` was renamed from the older `scoria_axi4_ifc`; some andesite pages and earlier scoria docs still use the old name. The module is the same pumice logic carried forward.
