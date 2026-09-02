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

# AXI4 Slave Read Interface (Clock-Gated)

**Module:** `axi4_slave_rd_cg.sv`
**Base Module:** [axi4_slave_rd](./axi4_slave_rd.md)
**Location:** `rtl/amba/axi4/`
**Status:** Production Ready

---

## Overview

This is the **clock-gated variant** of [axi4_slave_rd](./axi4_slave_rd.md) — same elastic buffer, with activity-based clock gating wrapped around it for power.

For complete clock-gating documentation, usage examples, and configuration guidelines, see the **[Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**.

What the wrapper buys you:

- **Same Functionality:** 100% equivalent to base module
- **Power Savings:** traffic-dependent; unmeasured in this repo -- treat any percentage as a placeholder until characterized
- **Configurable at runtime:** `cfg_cg_enable` / `cfg_cg_idle_count` inputs
- **Zero Overhead When Disabled:** `cfg_cg_enable=0` bypasses the gate

---

## Parameters

In addition to all [axi4_slave_rd](./axi4_slave_rd.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown, sizing `cfg_cg_idle_count` |
| `SKID_DEPTH_AR` | `2` | Skid-buffer depth on the AR channel. Legal range 2..8 inclusive; odd depths are legal. |
| `SKID_DEPTH_R` | `4` | Skid-buffer depth on the R channel. Legal range 2..8 inclusive; odd depths are legal. |

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
| `ARSize` | `IW+AW+8+3+2+1+4+3+4+4+UW` |
| `RSize` | `IW+DW+2+1+UW` |

## Ports

| Port | Dir | Width | Description |
|---|---|---|---|
| `aclk` | In | 1 |  |
| `aresetn` | In | 1 |  |
| `cfg_cg_enable` | In | 1 |  |
| `cfg_cg_idle_count` | In | `[CG_IDLE_COUNT_WIDTH-1:0]` |  |
| `s_axi_arid` | In | `[IW-1:0]` |  |
| `s_axi_araddr` | In | `[AW-1:0]` |  |
| `s_axi_arlen` | In | `[7:0]` |  |
| `s_axi_arsize` | In | `[2:0]` |  |
| `s_axi_arburst` | In | `[1:0]` |  |
| `s_axi_arlock` | In | 1 |  |
| `s_axi_arcache` | In | `[3:0]` |  |
| `s_axi_arprot` | In | `[2:0]` |  |
| `s_axi_arqos` | In | `[3:0]` |  |
| `s_axi_arregion` | In | `[3:0]` |  |
| `s_axi_aruser` | In | `[UW-1:0]` |  |
| `s_axi_arvalid` | In | 1 |  |
| `s_axi_arready` | Out | 1 |  |
| `s_axi_rid` | Out | `[IW-1:0]` |  |
| `s_axi_rdata` | Out | `[DW-1:0]` |  |
| `s_axi_rresp` | Out | `[1:0]` |  |
| `s_axi_rlast` | Out | 1 |  |
| `s_axi_ruser` | Out | `[UW-1:0]` |  |
| `s_axi_rvalid` | Out | 1 |  |
| `s_axi_rready` | In | 1 |  |
| `fub_axi_arid` | Out | `[IW-1:0]` |  |
| `fub_axi_araddr` | Out | `[AW-1:0]` |  |
| `fub_axi_arlen` | Out | `[7:0]` |  |
| `fub_axi_arsize` | Out | `[2:0]` |  |
| `fub_axi_arburst` | Out | `[1:0]` |  |
| `fub_axi_arlock` | Out | 1 |  |
| `fub_axi_arcache` | Out | `[3:0]` |  |
| `fub_axi_arprot` | Out | `[2:0]` |  |
| `fub_axi_arqos` | Out | `[3:0]` |  |
| `fub_axi_arregion` | Out | `[3:0]` |  |
| `fub_axi_aruser` | Out | `[UW-1:0]` |  |
| `fub_axi_arvalid` | Out | 1 |  |
| `fub_axi_arready` | In | 1 |  |
| `fub_axi_rid` | In | `[IW-1:0]` |  |
| `fub_axi_rdata` | In | `[DW-1:0]` |  |
| `fub_axi_rresp` | In | `[1:0]` |  |
| `fub_axi_rlast` | In | 1 |  |
| `fub_axi_ruser` | In | `[UW-1:0]` |  |
| `fub_axi_rvalid` | In | 1 |  |
| `fub_axi_rready` | Out | 1 |  |
| `cg_gating` | Out | 1 |  |
| `cg_idle` | Out | 1 |  |

---

## Functional Description

This wrapper is the base module plus one `amba_clock_gate_ctrl` instance. The
datapath is untouched -- every channel signal is forwarded verbatim -- so
functional behaviour is identical to the base module and the wrapper adds no
latency of its own.

What it adds is a gated clock. `amba_clock_gate_ctrl` watches two activity
terms, `user_valid` (this side's valids plus the base module's `busy`) and
`axi_valid` (the far side's valids), registers their OR into `r_wakeup`, and
stops the inner module's clock once both have been quiet for
`cfg_cg_idle_count` cycles. The clock restarts on the next activity, one cycle
later.

While the clock is stopped the wrapper masks its outward-facing READY signals
with `!cg_gating`, so a peer sees no acceptance until the clock runs again and
no handshake is lost across the wake boundary.

`cfg_cg_enable` arms this behaviour; with it low the clock free-runs and the
module is indistinguishable from its base.

---

## Timing Characteristics

| Skid parameter | Default depth |
|---|---|
| `SKID_DEPTH_AR` | 2 entries |
| `SKID_DEPTH_R` | 4 entries |

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
axi4_slave_rd_cg #(
    // Base module parameters (see axi4_slave_rd.md)
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
    // ... all other ports same as axi4_slave_rd (except busy)
);
```

---

## Design Notes

**A peer's READY must never enter the activity term.** A consumer that parks
its response-ready high while idle is behaving correctly; folding that signal
into `user_valid` pins this block permanently awake and defeats gating
entirely -- silently, because function is unaffected. Ten wrappers in this
repository shipped that way and nothing failed until someone measured.
`val/amba/test_cg_peer_ready.py` parks the peer READY high, holds every VALID
low, and requires `cg_gating`. Canonical rule:
`vault/handbook/design/clock-gating-activity-terms.md`.

**`cfg_cg_enable` is not a kill switch.** It arms gating and reaches
`amba_clock_gate_ctrl` only; the datapath and any monitor enables are forwarded
untouched. With it low the clock free-runs and this module behaves exactly like
its base.

**Gating latency.** The clock stops `cfg_cg_idle_count` + 2 cycles after the
last bus activity -- the idle counter, plus one for the `r_wakeup` flop. Size
the idle count against your traffic's inter-burst gap: too small and the block
wakes constantly, too large and it never gates.

**Cost.** Five flops: `r_wakeup` plus `r_idle_counter` at `IDLE_CNTR_WIDTH`,
scaling as 1 + `CG_IDLE_COUNT_WIDTH`. The ICG itself is a latch or BUFGCE, not
fabric flops.

---

## Related Modules

- **Base Module Functionality:** [axi4_slave_rd.md](./axi4_slave_rd.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Testing

`val/amba/test_axi4_slave_rd_cg.py` exercises this module. It collects 1 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axi4_slave_rd_cg.py -v
```

---

## Navigation

- **[← Back to AXI4 Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
