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

# RAPIDS Beats Top Specification

**Module:** `rapids_beats_top.sv`
**Location:** `projects/components/dmas/rapids/rtl/top_beats/`
**Status:** Implemented

---

## Overview

`rapids_beats_top` is the synthesizable top-level integration of the RAPIDS
Beats accelerator. It wraps the register block, config-block adapter, and core
with a single APB slave for all software access, and adds optional AXI transaction
monitors whose events are merged with the core's descriptor-monitor packet and
delivered through a MonBus AXI-Lite group (error-drain slave, capture master,
and interrupt).

---

## Integration Datapath

### Figure 3.14.1: RAPIDS Beats Top Integration

```
   s_apb_* (APB4 slave)
        |
     apb4_slave  (APB -> cmd/rsp)
        |
   cmdrsp_router (address decode)
     |                         |
     | 0x000-0x03F             | 0x100+ (and 0x1000 MON)
     v                         v
  apbtodescr            peakrdl_to_cmdrsp
  (per-channel           |
   descriptor kickoff)   v
     |               rapids_regs  ---> hwif_out
     |                   |
     |                   v
     |            rapids_config_block  (hwif_out -> cfg_*)
     |                   |
     +---------> rapids_core_beats <---+
                        |
        core AXI rd/wr, descriptor-monitor packet
                        |
   USE_AXI_MONITORS ? insert axi4_master_rd_mon / axi4_master_wr_mon
                        |
     +------------------+------------------+
     | m_axi_rd    m_axi_wr   rd/wr mon packets + core mon packet
     |                        |
     |                   monbus_arbiter (3:1)
     |                        |
     |               monbus_axil_axil_group
     |                 |          |         |
     |          s_axil_err_*  m_axil_mon_*  mon_irq
     v
   (external memory)
```

### Address Decode

| Range | Target | Purpose |
|-------|--------|---------|
| 0x000-0x03F | `apbtodescr` | Per-channel descriptor kick-off |
| 0x100-0x3FF | `rapids_regs` (base) | Configuration / status registers |
| 0x1000+ | `rapids_regs` (MON regfile) | Monitor configuration / performance |

: Table 3.14.1: Top-Level Address Decode

Because the monitor regfile is at `0x1000`, the APB address bus must be at least
13 bits wide (`APB_ADDR_WIDTH >= 13`) to reach it.

---

## AXI Monitors (USE_AXI_MONITORS)

When `USE_AXI_MONITORS = 1`, an `axi4_master_rd_mon` is inserted on the read
master (`m_axi_rd`) and an `axi4_master_wr_mon` on the write master
(`m_axi_wr`). Their `monitor_packet_t` outputs are combined with the core's
descriptor-monitor packet (zero-extended to 128 bits) by a 3-input
`monbus_arbiter` (round-robin, with input/output skid buffers). The combined
stream feeds `monbus_axil_axil_group`, which provides:

- `s_axil_err_*` -- AXI-Lite (32-bit) **error-drain slave**: CPU reads captured
  error events from the error FIFO.
- `m_axil_mon_*` -- AXI-Lite (64-bit) **capture master**: bulk-writes the MonBus
  trace to system memory (base/limit/watermark from `cfg_mon_*`).
- `mon_irq` -- interrupt on error/threshold events.

When `USE_AXI_MONITORS = 0` the monitor taps are bypassed (core AXI passes
straight through to `m_axi_rd`/`m_axi_wr`), the core MonBus is dropped
(always-ready), and the AXI-Lite group outputs are tied off (`s_axil_err`
read-inactive, `m_axil_mon` write-inactive, `mon_irq = 0`).

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS        = 8;
parameter int DATA_WIDTH          = 512;
parameter int ADDR_WIDTH          = 64;
parameter int AXI_ID_WIDTH        = 8;
parameter int SRAM_DEPTH          = 4096;
parameter int APB_ADDR_WIDTH      = 12;   // must be >= 13 to reach MON regfile @ 0x1000
parameter int APB_DATA_WIDTH      = 32;
parameter bit USE_AXI_MONITORS    = 0;    // 1 = insert rd/wr monitors + MonBus group
parameter int MON_MAX_TRANSACTIONS = 16;
parameter int AR_MAX_OUTSTANDING  = 8;
parameter int AW_MAX_OUTSTANDING  = 8;
```

: Table 3.14.2: RAPIDS Beats Top Parameters

---

## Top-Level Interfaces

| Interface | Signals | Notes |
|-----------|---------|-------|
| Clock / reset | `aclk`, `aresetn`, `cam_clear` | Single clock domain; `cam_clear` for monitor CAMs |
| APB slave | `s_apb_paddr` (APB_ADDR_WIDTH), `s_apb_psel/penable/pwrite/pwdata/pstrb`, `s_apb_prdata/pready/pslverr` | 32-bit data |
| Descriptor AXI (master) | `m_axi_desc_ar*`, `m_axi_desc_r*` | 256-bit read data |
| Data read AXI (master) | `m_axi_rd_ar*`, `m_axi_rd_r*` | DATA_WIDTH; monitored when enabled |
| Data write AXI (master) | `m_axi_wr_aw*`, `m_axi_wr_w*`, `m_axi_wr_b*` | DATA_WIDTH; monitored when enabled |
| Sink fill | `snk_fill_alloc_*`, `snk_fill_valid/ready/id/data`, `snk_fill_space_free` | Network ingress |
| Source drain | `src_drain_data_avail/req/size`, `src_drain_valid/read/id/data` | Network egress |
| MonBus error-drain slave | `s_axil_err_ar*`, `s_axil_err_r*` | AXI-Lite, 32-bit read |
| MonBus capture master | `m_axil_mon_aw*`, `m_axil_mon_w*` (64-bit `wdata`), `m_axil_mon_b*` | AXI-Lite write |
| MonBus interrupt | `mon_irq` | Error/threshold interrupt |
| MonBus config | `cfg_mon_base_addr`, `cfg_mon_limit_addr`, `cfg_mon_flush_watermark` | Capture region + flush watermark |
| Status | `system_idle`, `sched_error[NC-1:0]` | Aggregate status |

: Table 3.14.3: Top-Level Interfaces

---

**Last Updated:** 2026-07-02
