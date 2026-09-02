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

# AXI4 Master Write Interface (Clock-Gated)

**Module:** `axi4_master_wr_cg.sv`
**Base Module:** [axi4_master_wr](./axi4_master_wr.md)
**Location:** `rtl/amba/axi4/`
**Status:** Production Ready

---

## Overview

Same module, smaller power bill. This is the **clock-gated variant** of [axi4_master_wr](./axi4_master_wr.md): functionally identical, with activity-based clock gating wrapped around it.

For complete clock-gating documentation, usage examples, and configuration guidelines, see the **[Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**.

What the wrapper buys you:

- **Same Functionality:** 100% equivalent to base module
- **Power Savings:** traffic-dependent; unmeasured in this repo -- treat any percentage as a placeholder until characterized
- **Configurable at runtime:** `cfg_cg_enable` / `cfg_cg_idle_count` inputs
- **Zero Overhead When Disabled:** `cfg_cg_enable=0` bypasses the gate

---

## Parameters

In addition to all [axi4_master_wr](./axi4_master_wr.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown, sizing `cfg_cg_idle_count` |
| `SKID_DEPTH_AW` | `2` | Skid-buffer depth on the AW channel. Legal range 2..8 inclusive; odd depths are legal. |
| `SKID_DEPTH_B` | `2` | Skid-buffer depth on the B channel. Legal range 2..8 inclusive; odd depths are legal. |
| `SKID_DEPTH_W` | `4` | Skid-buffer depth on the W channel. Legal range 2..8 inclusive; odd depths are legal. |

The gating controls are RUNTIME INPUTS, not parameters: `cfg_cg_enable`
and `cfg_cg_idle_count`; status outputs `cg_gating` / `cg_idle`. One
`amba_clock_gate_ctrl` gates the whole module -- no per-domain gates. The
base module's `busy` output is NOT re-exported (consumed internally as a
wake term). (The ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_*
interface this page once documented never existed.)

---

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `AXI_WSTRB_WIDTH` | `AXI_DATA_WIDTH / 8` |
| `AW` | `AXI_ADDR_WIDTH` |
| `DW` | `AXI_DATA_WIDTH` |
| `IW` | `AXI_ID_WIDTH` |
| `SW` | `AXI_WSTRB_WIDTH` |
| `UW` | `AXI_USER_WIDTH` |
| `AWSize` | `IW+AW+8+3+2+1+4+3+4+4+UW` |
| `WSize` | `DW+SW+1+UW` |
| `BSize` | `IW+2+UW` |

## Ports

| Port | Dir | Width | Description |
|---|---|---|---|
| `aclk` | In | 1 |  |
| `aresetn` | In | 1 |  |
| `cfg_cg_enable` | In | 1 |  |
| `cfg_cg_idle_count` | In | `[CG_IDLE_COUNT_WIDTH-1:0]` |  |
| `fub_axi_awid` | In | `[IW-1:0]` |  |
| `fub_axi_awaddr` | In | `[AW-1:0]` |  |
| `fub_axi_awlen` | In | `[7:0]` |  |
| `fub_axi_awsize` | In | `[2:0]` |  |
| `fub_axi_awburst` | In | `[1:0]` |  |
| `fub_axi_awlock` | In | 1 |  |
| `fub_axi_awcache` | In | `[3:0]` |  |
| `fub_axi_awprot` | In | `[2:0]` |  |
| `fub_axi_awqos` | In | `[3:0]` |  |
| `fub_axi_awregion` | In | `[3:0]` |  |
| `fub_axi_awuser` | In | `[UW-1:0]` |  |
| `fub_axi_awvalid` | In | 1 |  |
| `fub_axi_awready` | Out | 1 |  |
| `fub_axi_wdata` | In | `[DW-1:0]` |  |
| `fub_axi_wstrb` | In | `[SW-1:0]` |  |
| `fub_axi_wlast` | In | 1 |  |
| `fub_axi_wuser` | In | `[UW-1:0]` |  |
| `fub_axi_wvalid` | In | 1 |  |
| `fub_axi_wready` | Out | 1 |  |
| `fub_axi_bid` | Out | `[IW-1:0]` |  |
| `fub_axi_bresp` | Out | `[1:0]` |  |
| `fub_axi_buser` | Out | `[UW-1:0]` |  |
| `fub_axi_bvalid` | Out | 1 |  |
| `fub_axi_bready` | In | 1 |  |
| `m_axi_awid` | Out | `[IW-1:0]` |  |
| `m_axi_awaddr` | Out | `[AW-1:0]` |  |
| `m_axi_awlen` | Out | `[7:0]` |  |
| `m_axi_awsize` | Out | `[2:0]` |  |
| `m_axi_awburst` | Out | `[1:0]` |  |
| `m_axi_awlock` | Out | 1 |  |
| `m_axi_awcache` | Out | `[3:0]` |  |
| `m_axi_awprot` | Out | `[2:0]` |  |
| `m_axi_awqos` | Out | `[3:0]` |  |
| `m_axi_awregion` | Out | `[3:0]` |  |
| `m_axi_awuser` | Out | `[UW-1:0]` |  |
| `m_axi_awvalid` | Out | 1 |  |
| `m_axi_awready` | In | 1 |  |
| `m_axi_wdata` | Out | `[DW-1:0]` |  |
| `m_axi_wstrb` | Out | `[SW-1:0]` |  |
| `m_axi_wlast` | Out | 1 |  |
| `m_axi_wuser` | Out | `[UW-1:0]` |  |
| `m_axi_wvalid` | Out | 1 |  |
| `m_axi_wready` | In | 1 |  |
| `m_axi_bid` | In | `[IW-1:0]` |  |
| `m_axi_bresp` | In | `[1:0]` |  |
| `m_axi_buser` | In | `[UW-1:0]` |  |
| `m_axi_bvalid` | In | 1 |  |
| `m_axi_bready` | Out | 1 |  |
| `cg_gating` | Out | 1 |  |
| `cg_idle` | Out | 1 |  |

---

## Timing Characteristics

| Skid parameter | Default depth |
|---|---|
| `SKID_DEPTH_AW` | 2 entries |
| `SKID_DEPTH_W` | 4 entries |
| `SKID_DEPTH_B` | 2 entries |

Each channel traverses one `gaxi_skid_buffer`, which registers both `rd_valid`
and its storage. The **1-cycle input-to-output latency therefore applies on
every transfer, including the unstalled case** -- there is no combinational
bypass. Depth buys backpressure absorption, not throughput; full rate is
sustained once the pipeline is primed. Legal range is 2..8 inclusive, odd
values included.

Clocking: `aclk`, reset `aresetn` (active-low asynchronous).

No synthesis numbers are quoted here. Frequency and area depend on the target
device and the parameters you elaborate with; run your own build.

---

## Usage Examples
```systemverilog
axi4_master_wr_cg #(
    // Base module parameters (see axi4_master_wr.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    .cfg_cg_enable(1'b1),
    .cfg_cg_idle_count(4'd8),
    .cg_gating(), .cg_idle(),
    // ... all other ports same as axi4_master_wr (except busy)
);
```

---

## Related Modules

- **Base Module Functionality:** [axi4_master_wr.md](./axi4_master_wr.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Testing

`val/amba/test_axi4_master_wr_cg.py` exercises this module. It collects 1 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axi4_master_wr_cg.py -v
```

---

## Navigation

- **[← Back to AXI4 Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
