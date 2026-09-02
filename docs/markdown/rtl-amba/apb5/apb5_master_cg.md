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

# APB5 Master (Clock-Gated)

**Module:** `apb5_master_cg.sv`
**Location:** `rtl/amba/apb5/`
**Status:** Production Ready

---

## Overview

Clock-gated variant of the APB5 Master module. Wraps the base `apb5_master` with clock gating control logic to reduce dynamic power consumption during idle periods.

### Key Features

- All APB5 Master features (see [apb5_master](apb5_master.md))
- Automatic clock gating during idle periods
- Configurable idle threshold before gating
- Registered wake-up on new activity, through a glitch-free ICG cell
- Power consumption reduction for low-duty-cycle applications

---

## Parameters

| Parameter | Default | Description |
|---|---|---|
| `ADDR_WIDTH` | `32` |  |
| `DATA_WIDTH` | `32` |  |
| `PROT_WIDTH` | `3` |  |
| `AUSER_WIDTH` | `4` |  |
| `WUSER_WIDTH` | `4` |  |
| `RUSER_WIDTH` | `4` |  |
| `BUSER_WIDTH` | `4` |  |
| `CMD_DEPTH` | `6` |  |
| `RSP_DEPTH` | `6` |  |
| `ENABLE_PARITY` | `0` |  |
| `CG_IDLE_COUNT_WIDTH` | `4` |  |
| `STRB_WIDTH` | `DATA_WIDTH / 8` |  |
| `AW` | `ADDR_WIDTH` |  |
| `DW` | `DATA_WIDTH` |  |
| `SW` | `STRB_WIDTH` |  |
| `PW` | `PROT_WIDTH` |  |
| `AUW` | `AUSER_WIDTH` |  |
| `WUW` | `WUSER_WIDTH` |  |
| `RUW` | `RUSER_WIDTH` |  |
| `BUW` | `BUSER_WIDTH` |  |
| `ICW` | `CG_IDLE_COUNT_WIDTH` |  |
| `CPW` | `AW + DW + SW + PW + AUW + WUW + 1` |  |
| `RPW` | `DW + RUW + BUW + 2` |  |

---

## Ports

| Port | Dir | Width | Description |
|---|---|---|---|
| `pclk` | In | 1 |  |
| `presetn` | In | 1 |  |
| `cfg_cg_enable` | In | 1 |  |
| `cfg_cg_idle_count` | In | `[ICW-1:0]` |  |
| `m_apb_PSEL` | Out | 1 |  |
| `m_apb_PENABLE` | Out | 1 |  |
| `m_apb_PADDR` | Out | `[AW-1:0]` |  |
| `m_apb_PWRITE` | Out | 1 |  |
| `m_apb_PWDATA` | Out | `[DW-1:0]` |  |
| `m_apb_PSTRB` | Out | `[SW-1:0]` |  |
| `m_apb_PPROT` | Out | `[PW-1:0]` |  |
| `m_apb_PAUSER` | Out | `[AUW-1:0]` |  |
| `m_apb_PWUSER` | Out | `[WUW-1:0]` |  |
| `m_apb_PRDATA` | In | `[DW-1:0]` |  |
| `m_apb_PSLVERR` | In | 1 |  |
| `m_apb_PREADY` | In | 1 |  |
| `m_apb_PWAKEUP` | In | 1 |  |
| `m_apb_PRUSER` | In | `[RUW-1:0]` |  |
| `m_apb_PBUSER` | In | `[BUW-1:0]` |  |
| `m_apb_PWDATAPARITY` | Out | `[SW-1:0]` |  |
| `m_apb_PADDRPARITY` | Out | 1 |  |
| `m_apb_PCTRLPARITY` | Out | 1 |  |
| `m_apb_PRDATAPARITY` | In | `[SW-1:0]` |  |
| `m_apb_PREADYPARITY` | In | 1 |  |
| `m_apb_PSLVERRPARITY` | In | 1 |  |
| `cmd_valid` | In | 1 |  |
| `cmd_ready` | Out | 1 |  |
| `cmd_pwrite` | In | 1 |  |
| `cmd_paddr` | In | `[AW-1:0]` |  |
| `cmd_pwdata` | In | `[DW-1:0]` |  |
| `cmd_pstrb` | In | `[SW-1:0]` |  |
| `cmd_pprot` | In | `[PW-1:0]` |  |
| `cmd_pauser` | In | `[AUW-1:0]` |  |
| `cmd_pwuser` | In | `[WUW-1:0]` |  |
| `rsp_valid` | Out | 1 |  |
| `rsp_ready` | In | 1 |  |
| `rsp_prdata` | Out | `[DW-1:0]` |  |
| `rsp_pslverr` | Out | 1 |  |
| `rsp_pwakeup` | Out | 1 |  |
| `rsp_pruser` | Out | `[RUW-1:0]` |  |
| `rsp_pbuser` | Out | `[BUW-1:0]` |  |
| `parity_error_rdata` | Out | 1 |  |
| `parity_error_ctrl` | Out | 1 |  |
| `wakeup_pending` | Out | 1 |  |
| `apb_clock_gating` | Out | 1 |  |

---

## Functional Description
```mermaid
flowchart TB
    subgraph CG["Clock Gating Control"]
        wake["Activity Flop<br/>r_wakeup"]
        idle["Idle<br/>Counter"]
        gate["ICG<br/>Clock Gate"]
    end

    subgraph CORE["APB5 Master Core"]
        master["apb5_master"]
    end

    pclk["pclk"] --> gate
    gate -->|gated_pclk| master
    idle --> gate
    wake --> gate

    cmd_valid --> wake
    wake --> idle
    master --> m_apb

    cfg_cg_enable --> gate
    cfg_cg_idle_count --> idle

    gate -->|apb_clock_gating| status
```

---

### Additional Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CG_IDLE_COUNT_WIDTH | int | 4 | Width of idle counter (max idle = 2^N-1 cycles) |
| `CMD_DEPTH` | int | `6` | Command FIFO depth. |
| `ENABLE_PARITY` | bit | `0` | Enable APB5 parity generation and checking. |
| `RSP_DEPTH` | int | `6` | Response FIFO depth. |

All other parameters inherited from [apb5_master](apb5_master.md).

---

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `STRB_WIDTH` | `DATA_WIDTH / 8` |
| `AW` | `ADDR_WIDTH` |
| `DW` | `DATA_WIDTH` |
| `SW` | `STRB_WIDTH` |
| `PW` | `PROT_WIDTH` |
| `AUW` | `AUSER_WIDTH` |
| `WUW` | `WUSER_WIDTH` |
| `RUW` | `RUSER_WIDTH` |
| `BUW` | `BUSER_WIDTH` |
| `ICW` | `CG_IDLE_COUNT_WIDTH` |
| `CPW` | `AW + DW + SW + PW + AUW + WUW + 1` |
| `RPW` | `DW + RUW + BUW + 2` |

### Additional Ports

### Clock Gating Configuration

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| cfg_cg_enable | 1 | Input | Enable clock gating (0=disabled, clock always runs) |
| cfg_cg_idle_count | CG_IDLE_COUNT_WIDTH | Input | Idle cycles before gating |

### Clock Gating Status

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| apb_clock_gating | 1 | Output | High while the internal clock is gated off |

There is no cumulative gated-cycle counter port on this module. If a gated-cycle
total is needed, count `apb_clock_gating` in the integrating logic on the
ungated `pclk`.

All ports of [apb5_master](apb5_master.md) -- including the parity signals,
`parity_error_rdata`, `parity_error_ctrl` and `wakeup_pending` -- are present
unchanged and pass straight through to the wrapped core.

### Clock Gating Behavior

### Gating State Machine

```mermaid
stateDiagram-v2
    [*] --> RUNNING

    RUNNING --> COUNTING : No activity
    COUNTING --> RUNNING : Activity detected
    COUNTING --> GATED : count >= threshold
    GATED --> RUNNING : cmd_valid or activity

    state RUNNING {
        note right of RUNNING : Clock running
    }
    state COUNTING {
        note right of COUNTING : Counting idle cycles
    }
    state GATED {
        note right of GATED : Clock stopped
    }
```

### Activity Detection and Wake-up Latency

The wrapper keeps the clock running whenever any of the following is high:

```
cmd_valid || rsp_valid || m_apb_PSEL || m_apb_PENABLE || m_apb_PWAKEUP
```

That term is registered into `r_wakeup` on the ungated `pclk`, and
`amba_clock_gate_ctrl` registers it once more before it reaches the gating
condition. Activity is registered once (AXI4, AXI5, AXI4-Lite, AXI4-Stream) or
twice (APB, APB5, AXI5-Stream) before reaching the ICG enable, which is
combinational. APB5 is a **two-stage** family, so the first gated-clock rising
edge available to the wrapped `apb5_master` arrives **3 ungated `pclk` cycles**
after activity asserts. Nothing is lost during those cycles -- the core is simply
held static, and the APB transfer stretches by that many wait states.

The actual gating element is an ICG (integrated clock gating) cell instantiated
by `clock_gate_ctrl`, not a bare AND gate, so enable changes are glitch-free.
Note that ICG cells are an ASIC-library primitive; on FPGA targets a clock-enable
approach should be used instead.

Gating engages `cfg_cg_idle_count + 1` ungated `pclk` cycles after the internal
wakeup deasserts, which is `cfg_cg_idle_count + 3` cycles after the last bus
activity, because APB5 adds two register stages ahead of the ICG enable. With the
default `CG_IDLE_COUNT_WIDTH=4` the maximum programmable idle threshold is 15
cycles.

### Timing

<!-- TODO: Add wavedrom timing diagram for clock gating -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - pclk
> - gated_pclk
> - cmd_valid
> - cfg_cg_idle_count
> - idle_counter
> - apb_clock_gating
> - Transaction before/after gating
## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
```systemverilog
apb5_master_cg #(
    .ADDR_WIDTH         (32),
    .DATA_WIDTH         (32),
    .AUSER_WIDTH        (4),
    .WUSER_WIDTH        (4),
    .CG_IDLE_COUNT_WIDTH(4)
) u_apb5_master_cg (
    .pclk               (apb_clk),
    .presetn            (apb_rst_n),

    // Clock gating configuration
    .cfg_cg_enable      (1'b1),
    .cfg_cg_idle_count  (4'd8),    // Gate after 8 idle cycles

    // Clock gating status
    .apb_clock_gating   (master_clk_gated),

    // APB5 and command/response interfaces
    // ... (same as apb5_master)
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

### Power Savings

The figures below are first-order expectations derived from the fraction of
cycles the clock is gated off; they are analytical estimates, not measured
silicon or post-layout power numbers. Actual savings depend on the technology
library, the ICG cell, and the clock-tree share of total dynamic power.

| Traffic Pattern | Duty Cycle | Estimated Dynamic Savings |
|-----------------|------------|---------------------------|
| Burst | 30% | 35-40% |
| Mixed | 50% | 20-25% |
| Continuous | 90%+ | <5% |
## Related Modules
- **[APB5 Master](apb5_master.md)** - Base module documentation
- **[APB5 Slave CG](apb5_slave_cg.md)** - Clock-gated slave
- **[Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)** - General clock gating concepts

---

## Testing

`val/amba/test_apb5_master_cg.py` exercises this module. It collects 3 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_apb5_master_cg.py -v
```

---

## Navigation

- **[← Back to APB5 Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
