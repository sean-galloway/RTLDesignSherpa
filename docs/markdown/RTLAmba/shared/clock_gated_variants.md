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

# Clock-Gated Variants Guide

**Category:** Infrastructure Documentation
**Location:** `rtl/amba/shared/amba_clock_gate_ctrl.sv`, `rtl/common/clock_gate_ctrl.sv`
**Applies To:** All AMBA modules with a `_cg` suffix
**Status:** Production Ready (transport modules) — see [Known Gaps](#known-gaps) for monitor variants

---

## Overview

Most AMBA protocol modules have a clock-gated (`_cg`) variant that wraps the base module,
drives it from a gated clock, and gates that clock after a programmable idle period. The
gating decision is made entirely at runtime through configuration inputs — there is no
compile-time enable parameter on the wrapper.

**Naming Convention:** `{base_module}_cg.sv`

**Examples:**
- `axi4_master_rd.sv` → `axi4_master_rd_cg.sv`
- `apb_slave.sv` → `apb_slave_cg.sv`
- `axis_master.sv` → `axis_master_cg.sv`

---

## Key Principle

**Clock-gated variants preserve the functional behavior of the base module and add runtime power management.**

```
Base Module + amba_clock_gate_ctrl + activity detection = _cg Variant
```

All base-module parameters and ports are preserved. The wrapper adds one parameter, two
configuration inputs, and one or two status outputs.

Note that a `_cg` variant is not cycle-identical to its base module. Most `_cg` wrappers
force the relevant `*ready` signals low while the clock is gated, so the first transfer
that arrives out of a gated period is backpressured for the wake-up cycle. Transfers are
delayed, never dropped. See [Wake-Up Behavior](#wake-up-behavior).

---

## Gating Infrastructure

The gating logic lives in two shared modules, not in the wrappers themselves.

### amba_clock_gate_ctrl (`rtl/amba/shared/`)

The AMBA-facing adapter. It ORs the two activity inputs, registers the result into
`r_wakeup`, exposes `idle = ~r_wakeup`, and passes `r_wakeup` to the generic controller.

| Port | Direction | Description |
|------|-----------|-------------|
| `clk_in` | Input | Ungated clock |
| `aresetn` | Input | Asynchronous active-low reset |
| `cfg_cg_enable` | Input | Global gating enable (0 = clock always runs) |
| `cfg_cg_idle_count` | Input | Idle countdown value, `CG_IDLE_COUNT_WIDTH` bits |
| `user_valid` | Input | Any user-side valid/activity signal |
| `axi_valid` | Input | Any bus-side valid/activity signal |
| `clk_out` | Output | Gated clock |
| `gating` | Output | Clock currently gated |
| `idle` | Output | No activity seen in the previous cycle |

### clock_gate_ctrl (`rtl/common/`)

The generic countdown controller. It loads `cfg_cg_idle_count` on reset, on `wakeup`, and
whenever `cfg_cg_enable` is low; otherwise it decrements to zero and holds. The gate
condition is:

```systemverilog
w_gate_enable = cfg_cg_enable && !wakeup && (r_idle_counter == 0);
```

`w_gate_enable` drives the `icg` cell (inverted, since the cell enable is active-high) and
is also driven out as `gating`.

---

## Additional Parameter (All _cg Modules)

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle counter. Maximum idle count is `2**CG_IDLE_COUNT_WIDTH - 1` (15 cycles at the default width). Sets the width of `cfg_cg_idle_count`. |

`CG_IDLE_COUNT_WIDTH` is a counter **width**, not a cycle count. To change the idle
threshold at runtime, drive `cfg_cg_idle_count`; widen `CG_IDLE_COUNT_WIDTH` only when the
threshold you need exceeds the current counter range.

**All other parameters are identical to the base module.**

---

## Additional Ports (All _cg Modules)

### Configuration Inputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Enable clock gating. `0` = clock always runs (runtime bypass). |
| `cfg_cg_idle_count` | Input | `CG_IDLE_COUNT_WIDTH` | Idle countdown value. Gating engages `cfg_cg_idle_count + 1` clocks after the internal wakeup deasserts, which is `cfg_cg_idle_count + 2` clocks after the last bus activity on single-stage families and `+ 3` on two-stage families. See [Gating Latency](#gating-latency). |

### Status Outputs

Status port naming differs by protocol family. Check the module port list before wiring.

| Family | Status Ports |
|--------|--------------|
| AXI4, AXI5, AXI4-Lite, AXI-Stream (`axis4`) | `cg_gating`, `cg_idle` |
| AXI5 monitor (`*_mon_cg`) | `cg_gating`, `cg_idle` |
| AXI5-Stream (`axis5`) | `axis_clock_gating` |
| APB, APB5 (non-CDC) | `apb_clock_gating` (the controller `idle` output is left unconnected) |
| APB5 CDC (`apb5_slave_cdc_cg`) | `apb_clock_gating` |
| APB CDC (`apb_slave_cdc_cg`) | `pclk_cg_gating`, `pclk_cg_idle`, `aclk_cg_gating`, `aclk_cg_idle` (two gating domains, two controller instances) |

**All other ports are identical to the base module.**

### Ports That Do Not Exist

These are common misconceptions; none of them are present in the RTL:

- **No `cg_clk_count` / gated-cycle counter.** The wrappers expose instantaneous state
  only. Accumulate `cg_gating` externally if a power metric is needed — see
  [Measuring Gated Cycles](#measuring-gated-cycles).
- **No scan or test-bypass port.** For DFT, hold `cfg_cg_enable` low
  (`.cfg_cg_enable(~scan_mode)`).
- **No `ENABLE_CLOCK_GATING`, `CG_IDLE_CYCLES`, or `CG_GATE_*` parameters** on any
  transport-level `_cg` module. Those names appear only in the legacy AXI4 and AXI4-Lite
  `*_mon_cg` wrappers described under [Known Gaps](#known-gaps).

---

## Clock Gating Behavior

### Activity Detection

Each wrapper builds `user_valid` and `axi_valid` from the valid signals (and, on the AXI
transport wrappers, the base module's `busy` output) of the channels it owns. For example,
`axi4_master_rd_cg`:

```systemverilog
assign user_valid = fub_axi_arvalid || fub_axi_rready || int_busy;
assign axi_valid  = m_axi_arvalid   || m_axi_rvalid;
```

### Gating Conditions (All Must Be True)

1. `cfg_cg_enable = 1`
2. The internal `r_wakeup` is deasserted (no activity in the previous cycle)
3. The idle counter has decremented to zero

### Counting Convention

Two numbers are quoted throughout this book, and they must not be confused:

- **Register stages** — how many flops an activity edge passes through before it reaches
  the ICG enable.
- **First usable gated-clock edge** — how many clocks after activity asserts before the
  gated block sees a rising edge it can work on. This is always one more than the register
  stage count, because the ICG enable itself is combinational and the released clock is
  only usable on the following edge.

Activity is registered once (AXI4, AXI5, AXI4-Lite, AXI4-Stream) or twice (APB, APB5,
AXI5-Stream) before reaching the ICG enable, which is combinational. The first gated-clock
rising edge available to the block therefore arrives **2 clocks** (single-stage families)
or **3 clocks** (two-stage families) after activity asserts.

`clock_gate_ctrl` itself adds **no** flop on the wake-up path: `w_gate_enable` is a
combinational function of `wakeup`, feeding the `icg` enable directly. Its header comment
"Wakeup: 1 clock from wakeup assertion to clock restoration" describes the resulting clock
edge, not a register stage.

### Register Stages by Family

| Family | Wrapper flop | `amba_clock_gate_ctrl` flop | Stages | First usable edge |
|--------|--------------|-----------------------------|--------|-------------------|
| AXI4, AXI5, AXI4-Lite `_cg` | No (combinational) | Yes | 1 | 2 clocks |
| `axis_master_cg`, `axis_slave_cg` (AXI4-Stream) | No (combinational) | Yes | 1 | 2 clocks |
| All `*_mon_cg` monitor wrappers | No (combinational) | Yes | 1 | 2 clocks |
| `apb_slave_cdc_cg` | No (combinational) | Yes | 1 | 2 clocks |
| `apb_master_cg`, `apb_slave_cg` | Yes | Yes | 2 | 3 clocks |
| `apb5_master_cg`, `apb5_slave_cg`, `apb5_slave_cdc_cg` | Yes | Yes | 2 | 3 clocks |
| `axis5_master_cg`, `axis5_slave_cg` (AXI5-Stream) | Yes | Yes | 2 | 3 clocks |

> **Note:** the AXI5-Stream `_cg` wrappers register activity locally and so behave like the
> APB family, not like the AXI4-Stream wrappers. Conversely `apb_slave_cdc_cg` drives the
> activity terms combinationally and so behaves like the AXI family. On both CDC wrappers
> the cross-domain activity term additionally pays the usual two-flop synchronizer delay in
> the receiving domain, on top of the stages counted above.

### Gating Latency

`gating` asserts `cfg_cg_idle_count + 1` clocks after the last cycle in which the internal
`wakeup` was high. Measured from the last bus activity, that is:

- `cfg_cg_idle_count + 2` clocks on the single-stage families (AXI4, AXI5, AXI4-Lite,
  AXI4-Stream, the monitor `_cg` wrappers, `apb_slave_cdc_cg`)
- `cfg_cg_idle_count + 3` clocks on the two-stage families (APB, APB5, AXI5-Stream)

The extra clock in each case is the time activity takes to appear on `r_wakeup`.

With `cfg_cg_idle_count = 0`, gating engages on the next clock after wakeup deasserts.

### Wake-Up Behavior

**Wake-up latency is not zero.** Activity is registered before it can release the gate.

**AXI4, AXI5, AXI4-Lite, AXI4-Stream:** the wrapper combines the valid signals
combinationally, so the only flop in the path is `r_wakeup` inside `amba_clock_gate_ctrl`
— **1 register stage, first usable clock edge 2 clocks** after activity asserts:

```
Cycle N:   Clock gated (cg_gating = 1). ARVALID asserts.
           user_valid = 1 combinationally; ARREADY forced low, so no handshake.
Cycle N+1: r_wakeup = 1 -> gate released combinationally, cg_gating = 0.
Cycle N+2: First usable gated-clock rising edge. ARREADY reflects the base
           module; the transfer can complete.
```

**APB, APB5, AXI5-Stream:** these wrappers register activity into their own `r_wakeup` flop
before handing it to `amba_clock_gate_ctrl`, which registers it again — **2 register
stages, first usable clock edge 3 clocks** after activity asserts.

### Ready Forcing While Gated

The following wrappers drive the relevant `*ready` outputs to zero while gated, so the
first beat out of a gated period is backpressured rather than lost:

- All AXI4, AXI5, and AXI4-Lite transport `_cg` modules
- `axis_master_cg`, `axis_slave_cg`
- All four AXI5 `*_mon_cg` modules
- `apb_slave_cdc_cg` (both clock domains)

`apb_master_cg`, `apb_slave_cg`, the APB5 variants, and the AXI5-Stream variants do not
force ready.

### State Machine

```mermaid
stateDiagram-v2
    [*] --> RUNNING

    RUNNING --> COUNTING : wakeup deasserted
    COUNTING --> RUNNING : activity detected<br/>(counter reloads)
    COUNTING --> GATED : counter reaches 0<br/>&& cfg_cg_enable
    GATED --> RUNNING : activity detected<br/>(1 stage / 2 clocks to first edge;<br/>2 stages / 3 clocks on APB, APB5, AXI5-Stream)

    state RUNNING {
        note right of RUNNING : Clock running, counter reloaded
    }

    state COUNTING {
        note right of COUNTING : Counter decrementing to 0
    }

    state GATED {
        note right of GATED : Clock stopped, ready forced low
    }
```

---

## Usage Patterns

### Pattern 1: Aggressive Gating

**Use Case:** Bursty traffic, low duty cycle, power-constrained systems.

```systemverilog
axi4_master_rd_cg #(
    // Base module parameters (same as the non-CG variant)
    .AXI_ID_WIDTH        (8),
    .AXI_ADDR_WIDTH      (32),
    .AXI_DATA_WIDTH      (64),

    // Clock gating
    .CG_IDLE_COUNT_WIDTH (4)          // counter range 0-15
) u_cg_aggressive (
    .aclk                (clk),
    .aresetn             (rst_n),

    .cfg_cg_enable       (1'b1),
    .cfg_cg_idle_count   (4'd1),      // gate 2 clocks after wakeup deasserts

    // ... all other ports same as the base module ...

    .cg_gating           (rd_gated),
    .cg_idle             (rd_idle)
);
```

### Pattern 2: Runtime-Adjustable Threshold

**Use Case:** A power-management controller trades wake-up cost against gated time.

```systemverilog
logic [3:0] idle_threshold;

always_comb begin
    case (power_mode)
        POWER_HIGH_PERF: idle_threshold = 4'd15;  // conservative
        POWER_BALANCED:  idle_threshold = 4'd5;   // moderate
        POWER_LOW:       idle_threshold = 4'd1;   // aggressive
        default:         idle_threshold = 4'd5;
    endcase
end

axi4_master_wr_cg #(
    .CG_IDLE_COUNT_WIDTH (4)
) u_cg_dynamic (
    .cfg_cg_enable       (power_mgmt_enable),
    .cfg_cg_idle_count   (idle_threshold),
    .cg_gating           (wr_gated),
    .cg_idle             (wr_idle)
    // ... base module ports ...
);
```

### Pattern 3: Gating Bypassed

**Use Case:** Functional verification, DFT scan, latency-critical operation.

```systemverilog
axi4_master_rd_cg #(
    .CG_IDLE_COUNT_WIDTH (4)
) u_cg_bypassed (
    .cfg_cg_enable       (1'b0),      // clock always runs
    .cfg_cg_idle_count   (4'd0),      // ignored while cfg_cg_enable = 0
    // ... base module ports ...
);
```

With `cfg_cg_enable = 0` the counter is continuously reloaded, `gating` stays low, the ICG
enable stays high, and the ready-forcing terms resolve to the base module's own ready
signals. The wrapper is then behaviorally equivalent to the base module.

This is the only bypass mechanism. There is no separate scan or test-mode port.

---

## Measuring Gated Cycles

The wrappers do not count gated cycles. Accumulate the status output where the metric is
needed:

```systemverilog
logic [31:0] total_cycles, gated_cycles;

always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        total_cycles <= '0;
        gated_cycles <= '0;
    end else begin
        total_cycles <= total_cycles + 1'b1;
        if (cg_gating) gated_cycles <= gated_cycles + 1'b1;
    end
end

// Gated fraction = (gated_cycles / total_cycles) x 100%
```

Note that this counter must itself be clocked from an ungated clock.

---

## Synthesis and Portability

### The ICG Cell

`clock_gate_ctrl` instantiates a bare `icg` primitive by name:

```systemverilog
icg u_icg (
    .clk (clk_in),
    .en  (~w_gate_enable),
    .gclk(clk_out)
);
```

`rtl/common/icg.sv` provides a behavioral model (a low-phase `always_latch` on the enable
ANDed with the clock) that is correct for simulation and for a standard-cell flow where the
name maps to a library integrated clock gate.

**ASIC:** map `icg` to the foundry integrated clock-gating cell. Verify the enable setup
and hold requirements of the chosen cell, and add clock-gating checks to the timing
constraints.

**FPGA portability note:** the `icg` behavioral model is not an FPGA-friendly construct.
An inferred latch feeding an AND gate on a clock net will either be rejected or produce a
glitch-prone, unconstrained clock. For FPGA targets, either

- replace `icg` with a vendor clock-enable primitive (Xilinx `BUFGCE`, Intel
  `ALTCLKCTRL`, and equivalents), or
- hold `cfg_cg_enable` low and use the base (non-`_cg`) module, converting the gating
  intent into ordinary clock enables that the synthesis tool can infer.

This is a real portability constraint, not a tuning preference. Do not push a `_cg` variant
through an FPGA flow without addressing it.

---

## Verification Considerations

### Functional Verification

Hold `cfg_cg_enable` low for functional regression runs. This yields simpler waveforms,
faster simulation, and removes the wake-up backpressure cycle from the transfer timing.

### Gating Verification

For gating-specific tests, drive `cfg_cg_enable` high and:

1. Sweep `cfg_cg_idle_count` and confirm `cg_gating` asserts `cfg_cg_idle_count + 1` clocks
   after the last wakeup.
2. Confirm the wake-up latency — 1 register stage and a first usable gated-clock edge
   2 clocks after activity asserts, or 2 stages and 3 clocks on APB, APB5, and AXI5-Stream
   — and that no transfer is lost across a gate-to-ungate transition.
3. Confirm that `*ready` is low for the whole gated interval on the wrappers listed under
   [Ready Forcing While Gated](#ready-forcing-while-gated).
4. Confirm `cfg_cg_enable = 0` reproduces base-module timing exactly.

---

## Available Clock-Gated Variants

### Transport Modules (22)

Every module below instantiates `amba_clock_gate_ctrl` and takes `CG_IDLE_COUNT_WIDTH`,
`cfg_cg_enable`, and `cfg_cg_idle_count`.

| Protocol | Location | CG Variants |
|----------|----------|-------------|
| AXI4 | `rtl/amba/axi4/` | `axi4_master_rd_cg`, `axi4_master_wr_cg`, `axi4_slave_rd_cg`, `axi4_slave_wr_cg` |
| AXI5 | `rtl/amba/axi5/` | `axi5_master_rd_cg`, `axi5_master_wr_cg`, `axi5_slave_rd_cg`, `axi5_slave_wr_cg` |
| AXI4-Lite | `rtl/amba/axil4/` | `axil4_master_rd_cg`, `axil4_master_wr_cg`, `axil4_slave_rd_cg`, `axil4_slave_wr_cg` |
| APB | `rtl/amba/apb/` | `apb_master_cg`, `apb_slave_cg`, `apb_slave_cdc_cg` (two gating domains) |
| APB5 | `rtl/amba/apb5/` | `apb5_master_cg`, `apb5_slave_cg`, `apb5_slave_cdc_cg` |
| AXI-Stream | `rtl/amba/axis4/` | `axis_master_cg`, `axis_slave_cg` |
| AXI5-Stream | `rtl/amba/axis5/` | `axis5_master_cg`, `axis5_slave_cg` |

### Monitor Modules (12)

| Protocol | Location | CG Variants | Gating Implemented |
|----------|----------|-------------|--------------------|
| AXI5 | `rtl/amba/monitor/` | `axi5_master_rd_mon_cg`, `axi5_master_wr_mon_cg`, `axi5_slave_rd_mon_cg`, `axi5_slave_wr_mon_cg` | Yes |
| AXI4 | `rtl/amba/monitor/` | `axi4_master_rd_mon_cg`, `axi4_master_wr_mon_cg`, `axi4_slave_rd_mon_cg`, `axi4_slave_wr_mon_cg` | No — see [Known Gaps](#known-gaps) |
| AXI4-Lite | `rtl/amba/monitor/` | `axil4_master_rd_mon_cg`, `axil4_master_wr_mon_cg`, `axil4_slave_rd_mon_cg`, `axil4_slave_wr_mon_cg` | No — see [Known Gaps](#known-gaps) |

**Total:** 34 `_cg` modules, of which 26 implement clock gating.

---

## Known Gaps

The eight AXI4 and AXI4-Lite `*_mon_cg` wrappers predate `amba_clock_gate_ctrl` and use a
different, incomplete scheme. None of them instantiates `amba_clock_gate_ctrl`, and none of
them takes `CG_IDLE_COUNT_WIDTH`.

**AXI4 `*_mon_cg`** (`axi4_master_rd_mon_cg`, `axi4_master_wr_mon_cg`,
`axi4_slave_rd_mon_cg`, `axi4_slave_wr_mon_cg`):

- Carry legacy parameters `ENABLE_CLOCK_GATING`, `CG_IDLE_CYCLES`, `CG_GATE_MONITOR`,
  `CG_GATE_REPORTER`, `CG_GATE_TIMERS`, and legacy inputs `cfg_cg_idle_threshold`,
  `cfg_cg_force_on`, `cfg_cg_gate_monitor`, `cfg_cg_gate_reporter`, `cfg_cg_gate_timers`.
- Build per-domain gated clocks (`aclk_monitor`, `aclk_reporter`, `aclk_timers`) with
  combinational `always_comb` blocks rather than ICG cells.
- **Do not connect those gated clocks to anything.** The underlying monitor is instantiated
  with `.aclk(aclk)` and an in-source `TODO: Use aclk_monitor once ICG cells replace
  combinational gating`. The gating logic is therefore dead, and the
  `cg_monitor_gated`/`cg_reporter_gated`/`cg_timers_gated`/`cg_cycles_saved` outputs report
  a model that has no effect on the clock.

**AXI4-Lite `*_mon_cg`** (`axil4_master_rd_mon_cg`, `axil4_master_wr_mon_cg`,
`axil4_slave_rd_mon_cg`, `axil4_slave_wr_mon_cg`):

- Carry legacy parameters `ENABLE_CLOCK_GATING` and `CG_IDLE_CYCLES` plus inputs
  `cfg_cg_enable` and `cfg_cg_idle_threshold`.
- Contain no gating structure at all. `cfg_cg_enable` is folded into
  `cfg_monitor_enable`, and `cg_cycles_saved` is a plain idle-cycle counter.

**Implication:** treat the AXI4 and AXI4-Lite `*_mon_cg` modules as functionally equivalent
to their non-`_cg` base monitors for power purposes. They save no dynamic power today. The
AXI5 `*_mon_cg` modules are the reference for how a monitor CG wrapper should look.

---

## Related Documentation

- **Gating Controller:** [amba_clock_gate_ctrl.md](amba_clock_gate_ctrl.md)
- **Per-Protocol Guides:**
  - [AXI4 Clock Gating Guide](../axi4/axi4_clock_gating_guide.md)
  - [AXI4-Lite Clock Gating Guide](../axil4/axil4_clock_gating_guide.md)
  - [AXI-Stream Clock Gating Guide](../axis4/axis_clock_gating_guide.md)
- **Base Module Documentation:** see the per-protocol directories (`axi4/`, `axi5/`,
  `axil4/`, `apb/`, `apb5/`, `axis4/`, `axis5/`)
- **AMBA Overview:** [overview.md](../overview.md)

---

## Navigation

- **[← Back to Shared Infrastructure Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
