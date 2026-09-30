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

# Sink Data Path

**Module:** `snk_data_path.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/macro/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

The sink data path joins the per-channel SRAM controller to the AXI write engine. Data enters through the fill interface, waits in the channel's SRAM partition and leaves as AXI4 write bursts.

In RAPIDS every SRAM word carries the byte enables of its data. The fill interface widens from `DW` to `DW + SW` bits, where `SW = DW/8`, and the write engine drives `m_axi_wstrb` from the stored enables. Everything else, including the allocation protocol, the scheduler interface and the burst rules, is as in RAPIDS Beats.

### Key Features

- **Per-channel SRAM partitions:** flow control by allocation and space-free counts.
- **Byte enables stored with the data:** the SRAM is `DW + SW` bits wide.
- **AXI write engine:** 4 KB-safe, beat-aligned bursts. See [AXI Write Engine](../ch02_fub_blocks/04_axi_write_engine.md).
- **Scheduler integration:** beat counts in, issue and commit strobes out.

### Figure 3.3.1: Sink Data Path Block Diagram

```
                          snk_data_path
   fill_alloc_*  --->  +-----------------------------+
   fill_valid/id --->  |     snk_sram_controller     |
   fill_data           |   DATA_WIDTH = DW + SW      |
   {strb, data}        |   per-channel partitions    |
                       +--------------+--------------+
                                      | drain_data [DW+SW-1:0]
                                      |   [DW-1:0]     -> wdata
                                      |   [DW+SW-1:DW] -> wstrb
                                      v
                       +-----------------------------+
   sched_wr_*    <---> |      axi_write_engine       | ---> m_axi_aw / w / b
                       +-----------------------------+
```

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_CHANNELS` | 8 | Number of channels (alias `NC`). |
| `ADDR_WIDTH` | 64 | Address width (alias `AW`). |
| `DATA_WIDTH` | 512 | Data width in bits (alias `DW`). The board uses 256. |
| `AXI_ID_WIDTH` | 8 | AXI ID width (alias `IW`). |
| `SRAM_DEPTH` | 512 | Words per channel partition (alias `SD`). |
| `SEG_COUNT_WIDTH` | `$clog2(SRAM_DEPTH) + 1` | Space counter width (alias `SCW`). |
| `PIPELINE` | 1 | SRAM read pipeline setting. |
| `AW_MAX_OUTSTANDING` | 8 | AW commands the write engine may have in flight. |
| `W_PHASE_FIFO_DEPTH` | 64 | Depth of the write engine W-phase queue. |
| `B_PHASE_FIFO_DEPTH` | 16 | Depth of the write engine B-phase queue. |
| `CIW` | `$clog2(NC)` | Channel id width. |
| `SW` | `DW / 8` | Byte enables per beat. New in RAPIDS. |

: Table 3.3.1: Sink Data Path Parameters

---

## Interfaces

### Fill Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `fill_alloc_req` | input | 1 | Space allocation request. |
| `fill_alloc_size` | input | 8 | Beats to allocate. |
| `fill_alloc_id` | input | CIW | Channel to allocate in. |
| `fill_space_free` | output | NC x SCW | Free space per channel. |
| `fill_valid` | input | 1 | Fill beat valid. |
| `fill_ready` | output | 1 | Ready for a fill beat. |
| `fill_id` | input | CIW | Channel of the fill beat. |
| `fill_data` | input | DW + SW | `{byte enables, data}`. Bits `[DW-1:0]` are data. Bits `[DW+SW-1:DW]` are enables. |

: Table 3.3.2: Fill Interface

### Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_wr_xfer_beats` | input | 8 | Write burst size cap in beats, minus one. Renamed from `cfg_axi_wr_xfer`. |

: Table 3.3.3: Configuration

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_wr_valid` | input | NC | Channel requests writes. |
| `sched_wr_ready` | output | NC | Last burst of a descriptor committed. |
| `sched_wr_addr` | input | NC x AW | Working destination byte address. |
| `sched_wr_beats` | input | NC x 32 | Beats still to write. |
| `sched_wr_burst_len` | input | NC x 8 | Requested burst length. Not used for sizing. |
| `sched_wr_done_strobe` | output | NC | AW issued. |
| `sched_wr_beats_done` | output | NC x 32 | Beats in that AW. |
| `sched_wr_commit_strobe` | output | NC | B response received. |
| `sched_wr_commit_beats` | output | NC x 32 | Beats committed by that B. |
| `sched_wr_error` | output | NC | Sticky write error (bad B response). |

: Table 3.3.4: Scheduler Interface

### AXI4 Write Master

The write master is `m_axi_aw*`, `m_axi_w*` and `m_axi_b*` with `IW`-bit IDs and `DW`-bit data. See [AXI4 Interface Specification](../ch04_interfaces/01_axi4_interface_spec.md). `m_axi_wstrb` is `DW/8` bits and carries the stored byte enables.

---

## Byte Enable Path

1. The upstream stage presents `{strb, data}` on `fill_data` with `fill_valid`.
2. The SRAM controller stores the whole `DW + SW` word. It is instantiated with `DATA_WIDTH = DW + SW`.
3. The drain side returns the same word as `drain_data`.
4. `drain_data[DW-1:0]` goes to `axi_wr_sram_data` and `drain_data[DW+SW-1:DW]` goes to `axi_wr_sram_strb` on the write engine.
5. The write engine drives `m_axi_wdata` and `m_axi_wstrb` from those two.

The SRAM depth counts words, so capacity in beats is unchanged. Only the width grows, by one bit per data byte.

---

## Differences from RAPIDS Beats

| Item | RAPIDS Beats | RAPIDS |
|------|--------------|--------|
| `fill_data` width | `DW` | `DW + SW` |
| SRAM word width | `DW` | `DW + SW` |
| `m_axi_wstrb` | all ones | stored per-beat enables |
| Config port name | `cfg_axi_wr_xfer` | `cfg_axi_wr_xfer_beats` |
| Scheduler port names | `sched_wr`, `sched_wr_done`, `sched_wr_commit` | `sched_wr_beats`, `sched_wr_beats_done`, `sched_wr_commit_beats` |
| Fill allocation, drain, error export | | Unchanged |

: Table 3.3.5: Sink Data Path Delta

The beats chapter is [Sink Data Path](../../rapids_beats_mas/ch03_macro_blocks/03_sink_data_path.md). Its timing diagrams apply to the AW, W and B sequencing unchanged.

---

**Last Updated:** 2026-09-30
