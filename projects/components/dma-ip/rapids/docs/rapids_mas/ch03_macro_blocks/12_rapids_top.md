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

# RAPIDS Top

**Module:** `rapids_top.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/top/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

`rapids_top` is the synthesizable top level. It wraps [RAPIDS Core](09_rapids_core.md) with an APB4 register interface, two config blocks, the register file, per-channel bus meters and the MonBus AXI-Lite group. It has the same hierarchy as RAPIDS Beats. Only the beat-count unit names differ.

The byte-granular behavior is entirely below the top: the packet record nets are internal to the core halves, so the top port list has no new signals. The full port list is in [Top-Level Port List](../../rapids_beats_mas/ch01_overview/02_port_list.md) and the top integration description is in [RAPIDS Beats Top](../../rapids_beats_mas/ch03_macro_blocks/12_rapids_beats_top.md).

### Figure 3.12.1: Top Hierarchy

```
  s_apb_*  --> apb4_slave --> peakrdl_to_cmdrsp --> rapids_regs
                                                      |
                     rapids_config_block u_cfg_src <--+--> rapids_config_block u_cfg_snk
                                   |                              |
                                   +------------> rapids_core (u_core) <----> AXI / AXIS
                                                      |
        axi_bus_meter u_rd_bus_meter, u_wr_bus_meter  |  mon_*
                                                      v
                                       monbus_axil4_axil4_group (u_monbus_axil_group)
                                                      --> m_axil_mon_*, mon_irq, s_axil_err_*
```

---

## APB Address Map

The APB address is 13 bits. Bit 12 selects the half.

| Range | Content |
|-------|---------|
| `0x0000` to `0x003F` | Source staged descriptor addresses. |
| `0x0040` | Source kick-off, one single-pulse bit per channel. |
| `0x0040` to `0x0FFF` | Source configuration registers. |
| `0x1000` to `0x103F` | Sink staged descriptor addresses. |
| `0x1040` | Sink kick-off, one single-pulse bit per channel. |
| `0x1040` to `0x1FFF` | Sink configuration registers. |

: Table 3.12.1: APB Address Map

The monitor register windows sit at `+0x800` of each half's 4 KB space. With `USE_MON_REGS` clear the windows answer with an APB error, so a host can tell a build without monitors from a zero setting.

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_CHANNELS` | 8 | Channels. |
| `DATA_WIDTH` | 512 | Data width in bits. The board uses 256. |
| `ADDR_WIDTH` | 64 | Address width. |
| `AXI_ID_WIDTH` | 8 | AXI ID width. |
| `SRAM_DEPTH` | 4096 | Words per channel at the top. |
| `APB_ADDR_WIDTH`, `APB_DATA_WIDTH` | 13, 32 | APB widths. |
| `MON_MAX_TRANSACTIONS` | 16 | Monitor table depth. |
| `SNK_AXIS_MON_AGENT_ID`, `SRC_AXIS_MON_AGENT_ID` | 9, 10 | AXIS monitor agent ids. |
| `ACLK_MHZ` | 100 | Clock in MHz for the AXIS monitor tick. |
| `USE_AXI_MONITORS` | 1 | 0 omits the monitors and the MonBus AXI-Lite group. |
| `USE_ROW_COL_MAJOR_ADDRESSING` | 1 | 0 compiles out extended addressing. |
| `GEN_MON` | 1 | 0 omits the completion and error emitters. |
| `USE_MON_REGS` | `USE_AXI_MONITORS != 0` | Wire the monitor register windows. |
| `AR_MAX_OUTSTANDING`, `AW_MAX_OUTSTANDING` | 8 | Outstanding bursts. |
| `PIPELINE` | 1 | Write engine pipelining. |
| `AXIS_ID_WIDTH`, `AXIS_DEST_WIDTH`, `AXIS_USER_WIDTH` | 8, 4, 1 | AXIS side widths. |

: Table 3.12.2: Top Parameters

Clock and reset are `aclk` and `aresetn`. `cam_clear` synchronously clears the MonBus group transaction tables.

---

## Differences from RAPIDS Beats

| Item | RAPIDS Beats | RAPIDS |
|------|--------------|--------|
| Module | `rapids_beats_top` | `rapids_top` |
| Core instance | `rapids_core_beats` | `rapids_core` |
| Register file, APB map, config blocks | | Unchanged |
| Bus meter beat counters | `r_rd`, `r_wr` | `r_rd_beats`, `r_wr_beats` |
| Config nets | `*_xfer` | `*_xfer_beats` |
| Port list | | Unchanged |

: Table 3.12.3: Top Delta

The register-file field names `RD_XFER_BEATS` and `WR_XFER_BEATS` are the same in both designs. Their meaning is beats in both, since bursts are beat-based.

---

**Last Updated:** 2026-09-30
