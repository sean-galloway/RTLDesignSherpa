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

# Write Intake (`scoria_wr_intake`)

**Module:** `scoria_wr_intake.sv`
**Location:** `rtl/fub/`
**Category:** AXI4 write intake
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified

---

## Purpose

The write intake is the "dumb" AXI4 write slave that sits between the splitter and the write-data CAM. It handles protocol skid buffering, buffers AW metadata and W data in small FIFOs, maps the head address to `{rank,bank,row,col}`, and pushes the decoded command to the CAM. Ragged bursts are rejected here with a self-generated `SLVERR` response; padding is the splitter's job upstream.

The block intentionally does no scheduling, forwarding, or pointer management. Those live downstream in `scoria_wr_data_cam`.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `AXI_ID_WIDTH` | int | — | 8 | AXI ID width |
| `AXI_ADDR_WIDTH` | int | — | 32 | AXI address width |
| `AXI_DATA_WIDTH` | int | — | 64 | AXI data width |
| `AXI_USER_WIDTH` | int | — | 1 | AXI USER width |
| `NUM_RANKS` | int | 1+ | 1 | DRAM ranks |
| `NUM_BANKS` | int | 1+ | 8 | DRAM banks |
| `ROW_WIDTH` | int | — | 14 | Row address width |
| `COL_WIDTH` | int | — | 10 | Column address width |
| `BYTE_OFFSET_WIDTH` | int | — | 3 | log2(device word bytes) |
| `RAGGED_ASSERT` | int | 0..1 | 1 | enable `$error` on ragged bursts |
| `AXI_BEATS_PER_BURST` | int | power of 2 | 4 | AXI beats per DRAM burst |
| `AW_FIFO_DEPTH` | int | — | 4 | AW meta FIFO depth |
| `WDATA_FIFO_DEPTH` | int | — | 16 | write-data FIFO depth |
| `B_FIFO_DEPTH` | int | — | 4 | B response FIFO depth |
| `SKID_DEPTH_AW` | int | — | 2 | AW skid buffer depth |
| `SKID_DEPTH_W` | int | — | 4 | W skid buffer depth |
| `SKID_DEPTH_B` | int | — | 2 | B skid buffer depth |

: Table 2.6.1: Write intake parameters

## Interface

### AXI4 write slave

| Signal | Direction | Width | Description |
|---|---|---|---|
| `s_axi_awid` | in | `AXI_ID_WIDTH` | AXI AW ID |
| `s_axi_awaddr` | in | `AXI_ADDR_WIDTH` | AXI AW address |
| `s_axi_awlen` | in | 8 | AXI AW length |
| `s_axi_awsize` | in | 3 | AXI AW size |
| `s_axi_awburst` | in | 2 | AXI AW burst type |
| `s_axi_awlock` | in | 1 | AXI AW lock |
| `s_axi_awcache` | in | 4 | AXI AW cache |
| `s_axi_awprot` | in | 3 | AXI AW protection |
| `s_axi_awqos` | in | 4 | AXI AW QoS |
| `s_axi_awregion` | in | 4 | AXI AW region |
| `s_axi_awuser` | in | `AXI_USER_WIDTH` | AXI AW user |
| `s_axi_awvalid` | in | 1 | AXI AW valid |
| `s_axi_awready` | out | 1 | AXI AW ready |
| `aw_agg_i` | in | 1 | aggregation sideband from splitter |
| `aw_last_i` | in | 1 | final-sub sideband from splitter |
| `s_axi_wdata` | in | `AXI_DATA_WIDTH` | AXI W data |
| `s_axi_wstrb` | in | `AXI_DATA_WIDTH/8` | AXI W strobe |
| `s_axi_wlast` | in | 1 | AXI W last |
| `s_axi_wuser` | in | `AXI_USER_WIDTH` | AXI W user |
| `s_axi_wvalid` | in | 1 | AXI W valid |
| `s_axi_wready` | out | 1 | AXI W ready |
| `s_axi_bid` | out | `AXI_ID_WIDTH` | AXI B ID |
| `s_axi_bresp` | out | 2 | AXI B response |
| `s_axi_buser` | out | `AXI_USER_WIDTH` | AXI B user |
| `s_axi_bvalid` | out | 1 | AXI B valid |
| `s_axi_bready` | in | 1 | AXI B ready |

### Downstream write-command push

| Signal | Direction | Width | Description |
|---|---|---|---|
| `aw_push_valid_o` | out | 1 | push decoded command to CAM |
| `aw_push_ready_i` | in | 1 | CAM ready to accept |
| `aw_push_rank_o` | out | `RKW` | decoded rank |
| `aw_push_bank_o` | out | `BKW` | decoded bank |
| `aw_push_row_o` | out | `ROW_WIDTH` | decoded row |
| `aw_push_col_o` | out | `COL_WIDTH` | decoded column |
| `aw_push_id_o` | out | `AXI_ID_WIDTH` | command ID |
| `aw_push_qos_o` | out | 4 | command QoS |
| `aw_push_err_o` | out | 1 | ragged-burst flag |
| `aw_push_agg_o` | out | 1 | part of a split host burst |
| `aw_push_last_o` | out | 1 | final sub of the host burst |

### Write-data pop

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wdata_valid_o` | out | 1 | W data valid to DFI path |
| `wdata_ready_i` | in | 1 | DFI path ready |
| `wdata_o` | out | `AXI_DATA_WIDTH` | W data |
| `wstrb_o` | out | `AXI_DATA_WIDTH/8` | W strobe |
| `wlast_o` | out | 1 | W last |

### Write completion

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wr_done_valid_i` | in | 1 | downstream commit completion |
| `wr_done_id_i` | in | `AXI_ID_WIDTH` | completion ID |
| `wr_done_resp_i` | in | 2 | completion response |

: Table 2.6.2: Write intake interface

## Microarchitecture internals

The intake contains three main FIFOs plus a sideband FIFO for aggregation bits.

| FIFO | Depth | Width | Push / Pop policy |
|---|---|---|---|
| AW meta | `AW_FIFO_DEPTH` | `3+4+IW+AW` | push on `fub_awvalid && fub_awready`; pop to `aw_push_ready_i` |
| Aggregation sideband | `SKID_DEPTH_AW + AW_FIFO_DEPTH` | 2 | push on `s_axi_awvalid && s_axi_awready`; pop locked to AW-meta write |
| Write data | `WDATA_FIFO_DEPTH` | `1+SW+DW` | push on `fub_wvalid`; pop to `wdata_ready_i` |
| B response | `B_FIFO_DEPTH` | `2+IW` | push on error or `wr_done_valid_i`; pop to AXI B |

: Table 2.6.3: Write intake FIFOs

The `axi4_slave_wr` instance provides the protocol skid buffers. The aggregation sideband `aw_agg_i`/`aw_last_i` arrives aligned with `s_axi_aw` before the skid, so it is captured in a dedicated FIFO and replayed in lockstep with the AW-meta FIFO write.

Address mapping aligns the head address down to the AXI beat before calling `scoria_addr_mapper`:

```text
BEAT_BO = $clog2(AXI_DATA_WIDTH / 8)
w_map_addr_wr = {w_head_addr[AW-1:BEAT_BO], {BEAT_BO{1'b0}}}
```

This prevents double-counting byte offsets when a wide AXI beat spans multiple device words. The byte lanes inside a beat are already carried by WSTRB; an unaligned start address must not also shift the column.

Ragged-burst detection is:

```text
w_aw_err = ((fub_awlen + 1) != AXI_BEATS_PER_BURST)
```

A ragged burst sets `aw_push_err_o` and pushes a self-generated `SLVERR` into the B FIFO. Downstream drops the command rather than committing it.

## FSM policy

There is no state machine. AW push, W pop, and B pop are independent FIFO handshakes. The only arbitration is the B-response FIFO write: an error B takes priority over a coincident `wr_done_valid_i`.

## Timing

AW and W are buffered independently after the skid. The AW-meta FIFO head is decoded combinationally and pushed when the CAM is ready. The W-data FIFO pops when the downstream DFI path is ready. B responses pop when the AXI B channel is ready.

## Notes

- **RAGGED_ASSERT:** When non-zero, the intake emits `$error` for ragged bursts. This is disabled only for directed SLVERR tests.
- **B-priority collision:** The intake asserts `$error` if an error B and a `wr_done_valid_i` would collide in the same cycle. The RTL gives priority to the error B, but the collision should never happen in normal operation.
- **Parameter-name history:** Comments in the RTL document an earlier confusion between `DRAM_BEAT_WIDTH` and `GEAR`. In scoria, `DRAM_BEAT_WIDTH` is passed as the AXI width and `GEAR` is always one, so the effective beat count is simply `AXI_BEATS_PER_BURST`.
