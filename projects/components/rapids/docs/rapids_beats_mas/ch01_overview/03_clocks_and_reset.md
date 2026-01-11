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

# Clocks and Reset

**Module:** `rapids_core_beats.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Clock Domain

RAPIDS Beats operates in a single clock domain for simplified design and maximum throughput.

### Clock Specifications

| Parameter | Specification |
|-----------|---------------|
| Clock Signal | `clk` (also `axi_aclk` in some submodules) |
| Frequency Range | 100 - 500 MHz |
| Duty Cycle | 45% - 55% |
| Clock Jitter | < 100 ps peak-to-peak |

: Table 1.3.1: Clock Specifications

### Clock Distribution

```
                  clk (system clock)
                        |
    +-------------------+-------------------+
    |                   |                   |
    v                   v                   v
beats_scheduler    sink_data_path    source_data_path
_group_array            |                   |
    |              +----+----+         +----+----+
    |              |         |         |         |
    v              v         v         v         v
descriptor    snk_sram   axi_write  axi_read  src_sram
_engine       _ctrl      _engine    _engine   _ctrl
```

---

## Reset Specification

RAPIDS uses asynchronous assert, synchronous deassert reset methodology.

### Reset Signal

| Parameter | Specification |
|-----------|---------------|
| Reset Signal | `rst_n` (also `axi_aresetn` in some submodules) |
| Polarity | Active-low |
| Assert | Asynchronous (immediate) |
| Deassert | Synchronous (on rising clock edge) |
| Minimum Duration | 10 clock cycles |

: Table 1.3.2: Reset Specifications

### Reset Timing Diagram

### Figure 1.3.1: Reset Timing

```
              ____    ____    ____    ____    ____    ____    ____
    clk      |    |__|    |__|    |__|    |__|    |__|    |__|    |__
                    :       :       :       :       :       :
    rst_n    ‾‾‾‾‾‾‾\_______________________________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                    :  [1]  :       :       :  [2]  :       :
    internal_regs   X|======RESET VALUES============|=NORMAL OP====
                    :       :       :       :       :       :
    fsm_state       X|======IDLE====================|=ACTIVE=======

    [1] = Reset asserted (asynchronous)
    [2] = Reset deasserted (synchronous to clock rising edge)
```

**TODO:** Replace with simulation-generated waveform

---

## Reset Behavior

### On Reset Assert

All modules initialize to known states:

| Component | Reset State |
|-----------|-------------|
| Scheduler FSM | IDLE |
| Descriptor Engine | IDLE, FIFOs empty |
| AXI Read Engine | Idle, no outstanding transactions |
| AXI Write Engine | Idle, no outstanding transactions |
| SRAM Pointers | All zeros |
| Alloc/Drain Controllers | Empty, full space available |
| MonBus | No packets pending |

: Table 1.3.3: Reset States

### Reset Sequence

```
1. External reset asserted (rst_n = 0)
   - All flip-flops async reset
   - All outputs driven to safe states
   - No AXI transactions

2. System stabilization (minimum 10 cycles)
   - Clock running and stable
   - Configuration registers programmed (optional)

3. Reset deasserted (rst_n = 1, sync to clk rising edge)
   - FSMs begin operation
   - Ready to accept descriptors/data
```

---

## Configuration During Reset

Some configuration signals MUST be stable before reset deassertion:

| Signal | Requirement |
|--------|-------------|
| `cfg_channel_enable` | Stable before rst_n=1 |
| `cfg_sched_timeout_cycles` | Stable before rst_n=1 |
| `cfg_axi_rd_xfer_beats` | Stable before rst_n=1 |
| `cfg_axi_wr_xfer_beats` | Stable before rst_n=1 |

: Table 1.3.4: Configuration Timing Requirements

---

## Reset Macros

RAPIDS uses standardized reset macros from `reset_defs.svh`:

```systemverilog
`include "reset_defs.svh"

// Standard reset pattern
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
        r_counter <= '0;
    end else begin
        r_state <= w_next_state;
        r_counter <= w_next_counter;
    end
)
```

---

## Power-On Reset Considerations

- External reset should be held for minimum 10 clock cycles after clock is stable
- Configuration registers should be programmed before or during reset
- No AXI transactions until reset is deasserted and channels are enabled

---

**Last Updated:** 2025-01-10
