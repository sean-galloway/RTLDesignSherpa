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

# axis4_slave_cg

**Module:** `axis4_slave_cg.sv`
**Base Module:** [axis4_slave](./axis4_slave.md)
**Location:** `rtl/amba/axis4/`
**Status:** Production Ready

---

## Overview

`axis4_slave_cg` is the clock-gated variant of `axis4_slave`: the same
AXI4-Stream transport, wrapped in one `amba_clock_gate_ctrl` that stops the
inner module's clock while the stream is idle. Functionally it is
indistinguishable from `axis4_slave`; what it adds is the gating and the
`cg_gating` / `cg_idle` status outputs.

For complete clock-gating documentation — wakeup terms, ungating latency, configuration
guidelines — see the [AXIS4 Clock-Gated Variants Guide](./axis4_clock_gating_guide.md).

---

## Parameters

All of the [axis4_slave](./axis4_slave.md) parameters, plus one clock-gating parameter:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `SKID_DEPTH` | int | 4 | Skid buffer depth in entries (2..8 inclusive), passed directly to `gaxi_skid_buffer.DEPTH` |
| `AXIS_DATA_WIDTH` | int | 32 | AXI4-Stream data bus width in bits (must be a multiple of 8) |
| `AXIS_ID_WIDTH` | int | 8 | Stream ID width (0 to disable) |
| `AXIS_DEST_WIDTH` | int | 4 | Destination width (0 to disable) |
| `AXIS_USER_WIDTH` | int | 1 | User signal width (0 to disable) |
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle countdown counter (max idle = 2^N - 1 cycles) |

`CG_IDLE_COUNT_WIDTH` is the **only** additional parameter. Gating enable and the idle
threshold are **runtime inputs**, not parameters — they appear in the port list, not here.

> There is no `ENABLE_CLOCK_GATING` parameter, no `CG_IDLE_CYCLES` parameter, and no
> `CG_GATE_*` domain-enable family. There is a single gating domain covering the whole
> module. The `_cg` wrapper also **does not expose the base module's `busy` output** — it is
> consumed internally as a wakeup term.

> The base module's parameters are `SKID_DEPTH`, `AXIS_DATA_WIDTH`, `AXIS_ID_WIDTH`,
> `AXIS_DEST_WIDTH` and `AXIS_USER_WIDTH`. AXI4-Stream has no address channel, so there is
> no `AXI_ADDR_WIDTH`.

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

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `aclk` | 1 | Input | AXI4-Stream clock |
| `aresetn` | 1 | Input | AXI4-Stream active-low reset |

### Clock Gating Configuration

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cfg_cg_enable` | 1 | Input | Enable clock gating (0 = clock always running) |
| `cfg_cg_idle_count` | CG_IDLE_COUNT_WIDTH | Input | Idle cycles before gating engages |

### Slave AXI4-Stream Interface (Input from Interconnect)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `s_axis_tdata` | DW | Input | Stream data |
| `s_axis_tstrb` | SW | Input | Data strobes (byte-valid indicators) |
| `s_axis_tlast` | 1 | Input | Last transfer in packet |
| `s_axis_tid` | IW_WIDTH | Input | Stream ID (routing/reordering) |
| `s_axis_tdest` | DESTW_WIDTH | Input | Destination routing |
| `s_axis_tuser` | UW_WIDTH | Input | User-defined sideband |
| `s_axis_tvalid` | 1 | Input | Data valid |
| `s_axis_tready` | 1 | Output | Ready to accept data |

### Backend Interface (Output to Processing Logic)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `fub_axis_tdata` | DW | Output | Stream data (to backend) |
| `fub_axis_tstrb` | SW | Output | Data strobes |
| `fub_axis_tlast` | 1 | Output | Last transfer in packet |
| `fub_axis_tid` | IW_WIDTH | Output | Stream ID |
| `fub_axis_tdest` | DESTW_WIDTH | Output | Destination routing |
| `fub_axis_tuser` | UW_WIDTH | Output | User-defined sideband |
| `fub_axis_tvalid` | 1 | Output | Data valid (to backend) |
| `fub_axis_tready` | 1 | Input | Backend ready |

### Clock Gating Status

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cg_gating` | 1 | Output | Clock currently gated (1=gated, 0=running) |
| `cg_idle` | 1 | Output | No activity observed in the previous cycle |

> The `_cg` wrappers do not expose `busy`. The base module's `busy` output is consumed
> internally as one of the wakeup terms and is not brought out. Use `cg_idle` for
> system-level power sequencing instead. Apart from that substitution, and the two
> `cfg_cg_*` inputs above, the port list matches the base module.

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
axis4_slave_cg #(
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
) u_axis_slave_cg (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .cfg_cg_enable         (cfg_cg_enable),
    .cfg_cg_idle_count     (cfg_cg_idle_count),
    .s_axis_tdata          (s_axis_tdata),
    .s_axis_tstrb          (s_axis_tstrb),
    .s_axis_tlast          (s_axis_tlast),
    .s_axis_tid            (s_axis_tid),
    .s_axis_tdest          (s_axis_tdest),
    .s_axis_tuser          (s_axis_tuser),
    .s_axis_tvalid         (s_axis_tvalid),
    .s_axis_tready         (s_axis_tready),
    .fub_axis_tdata        (fub_axis_tdata),
    .fub_axis_tstrb        (fub_axis_tstrb),
    .fub_axis_tlast        (fub_axis_tlast),
    .fub_axis_tid          (fub_axis_tid),
    .fub_axis_tdest        (fub_axis_tdest),
    .fub_axis_tuser        (fub_axis_tuser),
    .fub_axis_tvalid       (fub_axis_tvalid),
    .fub_axis_tready       (fub_axis_tready),
    .cg_gating             (cg_gating),
    .cg_idle               (cg_idle)
);
```

### Quick Usage

```systemverilog
axis4_slave_cg #(
    // Base module parameters (see axis4_slave.md)
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

    // ... all AXI4-Stream ports same as axis4_slave ...

    // Clock gating status (replaces the base module's `busy` output)
    .cg_gating(clk_is_gated),
    .cg_idle(stream_idle)
);
```

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

### Summary

The `axis4_slave_cg` module adds power optimization to `axis4_slave` through activity-based clock gating:

- **Same Data Functionality:** Identical to the base module once the clock is running
- **Power Savings:** Estimated 25-70% depending on stream duty cycle (planning figure, not measured)
- **Configurable:** Runtime idle threshold and enable via `cfg_cg_*` inputs
- **Bypass When Disabled:** `cfg_cg_enable = 0` holds the clock permanently enabled, making the wrapper functionally identical to the base module

---

## Related Modules

Read out of the RTL, not curated: these are the
modules this one instantiates and the modules that instantiate it.

**Instantiates:**
- `amba_clock_gate_ctrl`
- `axis4_slave`

### Documentation

- **Base Module Functionality:** [axis4_slave.md](./axis4_slave.md)
- **Clock Gating Guide:** [axis4_clock_gating_guide.md](./axis4_clock_gating_guide.md) (AXIS4-specific)
- **Generic CG Architecture:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Testing

`val/amba/test_axis4_slave_cg.py` exercises this module. It collects 2 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axis4_slave_cg.py -v
```

---

## Navigation

- **[← Back to AXIS4 Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
