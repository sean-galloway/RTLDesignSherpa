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

# Top-Level Port List

**Module:** `rapids_core_beats.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Parameters

### Primary Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;               // Number of DMA channels
parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS);
parameter int ADDR_WIDTH = 64;                // Address bus width
parameter int DATA_WIDTH = 512;               // Data bus width
parameter int AXI_ID_WIDTH = 8;               // AXI ID width
parameter int SRAM_DEPTH = 512;               // SRAM depth per channel
parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
parameter int PIPELINE = 0;                   // Pipeline stages
parameter int AR_MAX_OUTSTANDING = 8;         // Max outstanding AR transactions
parameter int AW_MAX_OUTSTANDING = 8;         // Max outstanding AW transactions
parameter int W_PHASE_FIFO_DEPTH = 64;        // Write data FIFO depth
parameter int B_PHASE_FIFO_DEPTH = 16;        // Write response FIFO depth
```

: Table 1.2.1: Primary Parameters

### Monitor Bus Parameters

```systemverilog
parameter int DESC_MON_BASE_AGENT_ID = 16;    // 0x10 - Descriptor Engines (16-23)
parameter int SCHED_MON_BASE_AGENT_ID = 48;   // 0x30 - Schedulers (48-55)
parameter int DESC_AXI_MON_AGENT_ID = 8;      // 0x08 - Descriptor AXI Master Monitor
parameter int MON_UNIT_ID = 1;                // 0x1
parameter int MON_MAX_TRANSACTIONS = 16;
```

: Table 1.2.2: Monitor Bus Parameters

---

## Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock (100-500 MHz) |
| `rst_n` | input | 1 | Active-low asynchronous reset |

: Table 1.2.3: Clock and Reset Signals

---

## APB Programming Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `apb_valid` | input | NC | Per-channel kick-off valid |
| `apb_ready` | output | NC | Per-channel ready |
| `apb_addr` | input | NC x AW | Per-channel descriptor start address |

: Table 1.2.4: APB Programming Interface

---

## Configuration Interface

### Per-Channel Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable` | input | NC | Enable each channel |
| `cfg_channel_reset` | input | NC | Per-channel soft reset |

: Table 1.2.5: Per-Channel Configuration

### Scheduler Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_sched_enable` | input | 1 | Global scheduler enable |
| `cfg_sched_timeout_cycles` | input | 16 | Timeout threshold in cycles |
| `cfg_sched_timeout_enable` | input | 1 | Enable timeout detection |
| `cfg_sched_err_enable` | input | 1 | Enable error reporting |
| `cfg_sched_compl_enable` | input | 1 | Enable completion reporting |
| `cfg_sched_perf_enable` | input | 1 | Enable performance monitoring |

: Table 1.2.6: Scheduler Configuration

### Descriptor Engine Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_desceng_enable` | input | 1 | Global descriptor engine enable |
| `cfg_desceng_prefetch` | input | 1 | Enable descriptor prefetching |
| `cfg_desceng_fifo_thresh` | input | 4 | Prefetch FIFO threshold |
| `cfg_desceng_addr0_base` | input | AW | Address range 0 base |
| `cfg_desceng_addr0_limit` | input | AW | Address range 0 limit |
| `cfg_desceng_addr1_base` | input | AW | Address range 1 base |
| `cfg_desceng_addr1_limit` | input | AW | Address range 1 limit |

: Table 1.2.7: Descriptor Engine Configuration

### AXI Transfer Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_rd_xfer_beats` | input | 8 | AXI read burst length (beats) |
| `cfg_axi_wr_xfer_beats` | input | 8 | AXI write burst length (beats) |

: Table 1.2.8: AXI Transfer Configuration

---

## Status Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `system_idle` | output | 1 | All components idle |
| `descriptor_engine_idle` | output | NC | Per-channel descriptor engine idle |
| `scheduler_idle` | output | NC | Per-channel scheduler idle |
| `scheduler_state` | output | NC x 7 | Per-channel FSM state (one-hot) |
| `sched_error` | output | NC | Per-channel error flag |

: Table 1.2.9: Status Interface

---

## Sink Path Interface (Network to Memory)

### Fill Interface (External to SRAM)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_fill_alloc_req` | input | 1 | Allocation request |
| `snk_fill_alloc_size` | input | 8 | Size in beats to allocate |
| `snk_fill_alloc_id` | input | CIW | Channel ID for allocation |
| `snk_fill_space_free` | output | NC x SCW | Available space per channel |
| `snk_fill_valid` | input | 1 | Fill data valid |
| `snk_fill_ready` | output | 1 | Ready to accept fill data |
| `snk_fill_data` | input | DW | Fill data |
| `snk_fill_last` | input | 1 | Last beat of fill burst |
| `snk_fill_id` | input | CIW | Fill channel ID |

: Table 1.2.10: Sink Fill Interface

### Sink AXI Write Master

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_snk_axi_awid` | output | IW | Write address ID |
| `m_snk_axi_awaddr` | output | AW | Write address |
| `m_snk_axi_awlen` | output | 8 | Burst length (beats - 1) |
| `m_snk_axi_awsize` | output | 3 | Burst size |
| `m_snk_axi_awburst` | output | 2 | Burst type |
| `m_snk_axi_awvalid` | output | 1 | Write address valid |
| `m_snk_axi_awready` | input | 1 | Write address ready |
| `m_snk_axi_wdata` | output | DW | Write data |
| `m_snk_axi_wstrb` | output | DW/8 | Write strobes |
| `m_snk_axi_wlast` | output | 1 | Last write beat |
| `m_snk_axi_wvalid` | output | 1 | Write data valid |
| `m_snk_axi_wready` | input | 1 | Write data ready |
| `m_snk_axi_bid` | input | IW | Response ID |
| `m_snk_axi_bresp` | input | 2 | Write response |
| `m_snk_axi_bvalid` | input | 1 | Response valid |
| `m_snk_axi_bready` | output | 1 | Response ready |

: Table 1.2.11: Sink AXI Write Master Interface

---

## Source Path Interface (Memory to Network)

### Source AXI Read Master

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_src_axi_arid` | output | IW | Read address ID |
| `m_src_axi_araddr` | output | AW | Read address |
| `m_src_axi_arlen` | output | 8 | Burst length (beats - 1) |
| `m_src_axi_arsize` | output | 3 | Burst size |
| `m_src_axi_arburst` | output | 2 | Burst type |
| `m_src_axi_arvalid` | output | 1 | Read address valid |
| `m_src_axi_arready` | input | 1 | Read address ready |
| `m_src_axi_rid` | input | IW | Read data ID |
| `m_src_axi_rdata` | input | DW | Read data |
| `m_src_axi_rresp` | input | 2 | Read response |
| `m_src_axi_rlast` | input | 1 | Last read beat |
| `m_src_axi_rvalid` | input | 1 | Read data valid |
| `m_src_axi_rready` | output | 1 | Read data ready |

: Table 1.2.12: Source AXI Read Master Interface

### Drain Interface (SRAM to External)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_drain_valid` | output | 1 | Drain data valid |
| `src_drain_ready` | input | 1 | External ready for drain |
| `src_drain_data` | output | DW | Drain data |
| `src_drain_last` | output | 1 | Last beat of drain burst |
| `src_drain_id` | output | CIW | Drain channel ID |

: Table 1.2.13: Source Drain Interface

---

## Descriptor AXI Master

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_desc_axi_arid` | output | IW | Read address ID |
| `m_desc_axi_araddr` | output | AW | Read address |
| `m_desc_axi_arlen` | output | 8 | Burst length |
| `m_desc_axi_arsize` | output | 3 | Burst size |
| `m_desc_axi_arburst` | output | 2 | Burst type |
| `m_desc_axi_arvalid` | output | 1 | Read address valid |
| `m_desc_axi_arready` | input | 1 | Read address ready |
| `m_desc_axi_rid` | input | IW | Read data ID |
| `m_desc_axi_rdata` | input | 256 | Descriptor data (256-bit) |
| `m_desc_axi_rresp` | input | 2 | Read response |
| `m_desc_axi_rlast` | input | 1 | Last read beat |
| `m_desc_axi_rvalid` | input | 1 | Read data valid |
| `m_desc_axi_rready` | output | 1 | Read data ready |

: Table 1.2.14: Descriptor AXI Master Interface

---

## MonBus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_valid` | output | 1 | Monitor packet valid |
| `monbus_ready` | input | 1 | Monitor consumer ready |
| `monbus_data` | output | 64 | Monitor packet data |

: Table 1.2.15: MonBus Interface

---

**Last Updated:** 2025-01-10
