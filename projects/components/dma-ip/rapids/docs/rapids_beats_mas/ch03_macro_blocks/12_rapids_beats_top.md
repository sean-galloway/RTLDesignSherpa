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
**Location:** `projects/components/dma-ip/rapids/rtl/top_beats/`
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

### Figure 3.12.1: RAPIDS Beats Top Integration

```
   s_apb_* (APB4 slave)
        |
     apb4_slave  (APB -> cmd/rsp)
        |
   cmdrsp_router (address decode)
        |
        | all ranges: 0x000-0x03F kick regs, 0x100+ base, 0x1000 MON
        v
                   peakrdl_to_cmdrsp
                         |
                         v
                   rapids_regs  ---> hwif_out
                         |
                         v
                   rapids_config_block  (hwif_out -> cfg_*)
                         |
                         v
                rapids_core_beats
                        |
        core AXI rd/wr, AXIS in/out, ONE merged MonBus stream
        (per half: scheduler groups + descriptor-read monlite +
         AXIS monlite through a 3:1 monbus_arbiter; core merges 2:1)
                        |
     +------------------+------------------+
     | m_axi_rd    m_axi_wr   s_axis / m_axis      core_mon_*
     |                                                 |
     |                                  monbus_axil4_axil4_group
     |                 |          |         |
     |          s_axil_err_*  m_axil_mon_*  mon_irq
     v
   (external memory)
```

### Address Decode

| Range | Target | Purpose |
|-------|--------|---------|
| 0x000-0x03F | `rapids_regs` (kick) | Per-channel descriptor kick-off registers |
| 0x100-0x3FF | `rapids_regs` (base) | Configuration / status registers |
| 0x1000+ | `rapids_regs` (MON regfile) | Monitor configuration / performance |

: Table 3.12.1: Top-Level Address Decode

Because the monitor regfile is at `0x1000`, the APB address bus must be at least
13 bits wide (`APB_ADDR_WIDTH >= 13`) to reach it.

---

## Write-engine pipelining (PIPELINE)

`PIPELINE` reaches `axi_write_engine_beats` through the core and both halves.
`0` is the engine's original contract, one burst in flight per channel; `1`
allows up to `AW_MAX_OUTSTANDING` per channel. Every module that declares the
parameter, from the engines to this top, defaults to `1` since 2026-09-28: once rapids BUG-005 made `PIPELINE = 0` honour one-in-flight, the
8-channel Genesys 2 build measured 49.9 % AXI4-wr engaged utilization at 4096
beats per channel (59.5 % at 1024), against 100 % on the bitstream before the
fix -- which had reached line rate only because the pre-fix engine ran two
bursts in flight by accident. The harness simulation reproduces the same
numbers (82.4 % at 1024 beats with `PIPELINE = 0`, 99.9 % with `1`). One
burst in flight cannot cover the write-response round trip at 8-beat bursts,
so `1` is the design point at every level; `0` is selectable for a design that
must bound each channel to a single outstanding write, never the default.

## AXI Monitors (USE_AXI_MONITORS)

When `USE_AXI_MONITORS = 1` the top builds the `monbus_axil4_axil4_group` and
feeds it the core's MonBus stream. That stream carries the scheduler groups'
completion and error events and two monitor-lite instances per half:
`axi4_master_rd_monlite` on the half's descriptor read master, inside
`scheduler_group_array_beats` (agent 0x08), and an AXIS monitor-lite on the
half's network port (rapids TASK-015): `axis4_slave_monlite` on the sink's
`s_axis_*` (agent 0x09, configured by `SNK.MON.WRMON_*`) and
`axis4_master_monlite` on the source's `m_axis_*` (agent 0x0A, configured by
`SRC.MON.RDMON_*`). Each half merges its scheduler array, its AXIS monitor and
a tied-off placeholder client in a 3:1 `monbus_arbiter`; the core merges the two
halves 2:1. The AXIS wrappers also place an `axis4_slave` / `axis4_master` skid
stage (depth 4) on the network port in every build; only the tap is gated by
`USE_AXI_MONITORS`. The data masters `m_axi_rd` and `m_axi_wr` carry NO
monitors (an earlier revision of this page said rd/wr monitor-lite blocks sat
on the data masters; the RTL has never had them). Data-master observation lives
in the characterization harness as external instruments (`axi_bus_meter`,
`axis_bus_meter`, and the interface observers on `USE_OBSERVERS` builds). The
group's AXIS filter slot is fed from `SRC.MON.RDMON_*`, so it filters both
halves' AXIS packets; `*_PKT_MASK` masks on a set bit and resets to all-masked
(rapids BUG-008 corrected its description). The group provides:

- `s_axil_err_*` -- AXI-Lite (32-bit) **error-drain slave**: CPU reads captured
  error events from the error FIFO.
- `m_axil_mon_*` -- AXI-Lite (64-bit) **capture master**: bulk-writes the MonBus
  trace to system memory (base/limit/watermark from `cfg_mon_*`).
- `mon_irq` -- interrupt on error/threshold events.

When `USE_AXI_MONITORS = 0` the descriptor and AXIS monitor-lites are omitted
(the AXIS skid stages stay), the core
MonBus is dropped (always-ready), and the AXI-Lite group outputs are tied off
(`s_axil_err` read-inactive, `m_axil_mon` write-inactive, `mon_irq = 0`).

### Monitor registers on a monitors-off build (USE_MON_REGS)

`USE_MON_REGS` defaults to `USE_AXI_MONITORS != 0` and is passed to both config
blocks. When it is 0 the blocks strap every `cfg_*mon_*` output off, and the APB
path answers the two MON register windows -- SRC MON at 0x0800-0x0FFF and SNK MON
at 0x1800-0x1FFF, i.e. `paddr[11]` set in either 4 KB half -- with `PSLVERR` and
zero read data instead of letting the registers accept a write and read it back.
The address map does not change, so one host image still addresses both builds;
what changes is that "not built" is distinguishable from "built and set to zero".
A blocked access is still accepted (holding `cmd_ready` low would hang the bus)
and the guard's error beat replaces the adapter's response for that one transfer
(rapids ISSUE-003; the shape is STREAM's TASK-002 guard). With `USE_MON_REGS = 1`
the guard folds away to the straight-through wiring.

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
parameter bit USE_MON_REGS        = (USE_AXI_MONITORS != 0); // 0 = MON windows answer PSLVERR
parameter int MON_MAX_TRANSACTIONS = 16;
parameter int AR_MAX_OUTSTANDING  = 8;
parameter int AW_MAX_OUTSTANDING  = 8;
parameter int PIPELINE            = 1;   // write-engine pipelining; see the note below
```

: Table 3.12.2: RAPIDS Beats Top Parameters

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

: Table 3.12.3: Top-Level Interfaces

---

**Last Updated:** 2026-07-02
