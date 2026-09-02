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

# AXIS Master Interface (Clock-Gated)

**Module:** `axis_master_cg.sv`
**Base Module:** [axis_master](./axis_master.md)
**Location:** `rtl/amba/axis4/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axis_master](./axis_master.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [AXIS4 Clock-Gated Variants Guide](./axis_clock_gating_guide.md)**

---

## Summary

The `axis_master_cg` module adds power optimization to `axis_master` through activity-based clock gating:

- **Same Data Functionality:** Identical to the base module once the clock is running
- **Power Savings:** Estimated 25-70% depending on stream duty cycle (planning figure, not measured)
- **Configurable:** Runtime idle threshold and enable via `cfg_cg_*` inputs
- **Bypass When Disabled:** `cfg_cg_enable = 0` holds the clock permanently enabled, making the wrapper functionally identical to the base module

---

## Common Parameters

In addition to all [axis_master](./axis_master.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown counter (max idle = 2^N - 1 cycles) |

This is the **only** additional parameter. Gating enable and the idle threshold are
**runtime inputs**, not parameters:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Enable clock gating (0 = clock always running) |
| `cfg_cg_idle_count` | Input | `CG_IDLE_COUNT_WIDTH` | Idle cycles before gating engages |
| `cg_gating` | Output | 1 | Clock currently gated |
| `cg_idle` | Output | 1 | No activity observed in the previous cycle |

> There is no `ENABLE_CLOCK_GATING` parameter, no `CG_IDLE_CYCLES` parameter, and no
> `CG_GATE_*` domain-enable family. There is a single gating domain covering the whole
> module. The `_cg` wrapper also **does not expose the base module's `busy` output** — it is
> consumed internally as a wakeup term.

---

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `DW` | `AXIS_DATA_WIDTH` |
| `IW` | `AXIS_ID_WIDTH` |
| `DESTW` | `AXIS_DEST_WIDTH` |
| `UW` | `AXIS_USER_WIDTH` |
| `SW` | `DW / 8` |
| `IW_WIDTH` | `(IW > 0) ? IW : 1` |
| `DESTW_WIDTH` | `(DESTW > 0) ? DESTW : 1` |
| `UW_WIDTH` | `(UW > 0) ? UW : 1` |

## Quick Usage

```systemverilog
axis_master_cg #(
    // Base module parameters (see axis_master.md)
    .SKID_DEPTH(4),
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(1),

    // Clock gating (see CG guide for details)
    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),

    // Clock gating control (runtime inputs)
    .cfg_cg_enable(cg_enable),
    .cfg_cg_idle_count(4'd8),

    // ... all AXI4-Stream ports same as axis_master ...

    // Clock gating status (replaces the base module's `busy` output)
    .cg_gating(clk_is_gated),
    .cg_idle(stream_idle)
);
```

> The base module's parameters are `SKID_DEPTH`, `AXIS_DATA_WIDTH`, `AXIS_ID_WIDTH`,
> `AXIS_DEST_WIDTH` and `AXIS_USER_WIDTH`. AXI4-Stream has no address channel, so there is
> no `AXI_ADDR_WIDTH`.

---

## Documentation

- **Base Module Functionality:** [axis_master.md](./axis_master.md)
- **Clock Gating Guide:** [axis_clock_gating_guide.md](./axis_clock_gating_guide.md) (AXIS4-specific)
- **Generic CG Architecture:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Parameters

| Parameter | Default | Description |
|---|---|---|
| `SKID_DEPTH` | `4` |  |
| `AXIS_DATA_WIDTH` | `32` |  |
| `AXIS_ID_WIDTH` | `8` |  |
| `AXIS_DEST_WIDTH` | `4` |  |
| `AXIS_USER_WIDTH` | `1` |  |
| `CG_IDLE_COUNT_WIDTH` | `4` |  |
| `DW` | `AXIS_DATA_WIDTH` |  |
| `IW` | `AXIS_ID_WIDTH` |  |
| `DESTW` | `AXIS_DEST_WIDTH` |  |
| `UW` | `AXIS_USER_WIDTH` |  |
| `SW` | `DW / 8` |  |
| `IW_WIDTH` | `(IW > 0` |  |
| `DESTW_WIDTH` | `(DESTW > 0` |  |
| `UW_WIDTH` | `(UW > 0` |  |

---

## Ports

| Port | Dir | Width | Description |
|---|---|---|---|
| `aclk` | In | 1 |  |
| `aresetn` | In | 1 |  |
| `cfg_cg_enable` | In | 1 |  |
| `cfg_cg_idle_count` | In | `[CG_IDLE_COUNT_WIDTH-1:0]` |  |
| `fub_axis_tdata` | In | `[DW-1:0]` |  |
| `fub_axis_tstrb` | In | `[SW-1:0]` |  |
| `fub_axis_tlast` | In | 1 |  |
| `fub_axis_tid` | In | `[IW_WIDTH-1:0]` |  |
| `fub_axis_tdest` | In | `[DESTW_WIDTH-1:0]` |  |
| `fub_axis_tuser` | In | `[UW_WIDTH-1:0]` |  |
| `fub_axis_tvalid` | In | 1 |  |
| `fub_axis_tready` | Out | 1 |  |
| `m_axis_tdata` | Out | `[DW-1:0]` |  |
| `m_axis_tstrb` | Out | `[SW-1:0]` |  |
| `m_axis_tlast` | Out | 1 |  |
| `m_axis_tid` | Out | `[IW_WIDTH-1:0]` |  |
| `m_axis_tdest` | Out | `[DESTW_WIDTH-1:0]` |  |
| `m_axis_tuser` | Out | `[UW_WIDTH-1:0]` |  |
| `m_axis_tvalid` | Out | 1 |  |
| `m_axis_tready` | In | 1 |  |
| `cg_gating` | Out | 1 | Active gating indicator |
| `cg_idle` | Out | 1 | All buffers empty indicator |

---

## Timing Characteristics

| Skid parameter | Default depth |
|---|---|
| `SKID_DEPTH` | 4 entries |

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

Every parameter and port below is taken from the module declaration.

```systemverilog
axis_master_cg #(
    .SKID_DEPTH            (4),
    .AXIS_DATA_WIDTH       (32),
    .AXIS_ID_WIDTH         (8),
    .AXIS_DEST_WIDTH       (4),
    .AXIS_USER_WIDTH       (1),
    .CG_IDLE_COUNT_WIDTH   (4),
    .DW                    (AXIS_DATA_WIDTH),
    .IW                    (AXIS_ID_WIDTH),
    .DESTW                 (AXIS_DEST_WIDTH),
    .UW                    (AXIS_USER_WIDTH)
) u_axis_master_cg (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .cfg_cg_enable         (cfg_cg_enable),
    .cfg_cg_idle_count     (cfg_cg_idle_count),
    .fub_axis_tdata        (fub_axis_tdata),
    .fub_axis_tstrb        (fub_axis_tstrb),
    .fub_axis_tlast        (fub_axis_tlast),
    .fub_axis_tid          (fub_axis_tid),
    .fub_axis_tdest        (fub_axis_tdest),
    .fub_axis_tuser        (fub_axis_tuser),
    .fub_axis_tvalid       (fub_axis_tvalid),
    .fub_axis_tready       (fub_axis_tready),
    .m_axis_tdata          (m_axis_tdata),
    .m_axis_tstrb          (m_axis_tstrb),
    .m_axis_tlast          (m_axis_tlast),
    .m_axis_tid            (m_axis_tid),
    .m_axis_tdest          (m_axis_tdest),
    .m_axis_tuser          (m_axis_tuser),
    .m_axis_tvalid         (m_axis_tvalid),
    .m_axis_tready         (m_axis_tready),
    .cg_gating             (cg_gating),
    .cg_idle               (cg_idle)
);
```

---

## Related Modules

Read out of the RTL, not curated: these are the
modules this one instantiates and the modules that instantiate it.

**Instantiates:**
- `amba_clock_gate_ctrl`
- `axis_master`

---

## Testing

`val/amba/test_axis_master_cg.py` exercises this module. It collects 2 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axis_master_cg.py -v
```

---

## Navigation

- **[← Back to AXIS4 Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
