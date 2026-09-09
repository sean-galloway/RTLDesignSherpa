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

# APB PIT 8254 - Architecture

## Overview

### High-Level Block Diagram

```
                                  apb4_pit_8254 (Top Level)
┌────────────────────────────────────────────────────────────────────────┐
│                                                                        │
│  ┌──────────────┐     ┌──────────────────┐     ┌──────────────────┐  │
│  │              │     │                  │     │                  │  │
│  │  apb4_slave   │────▶│  pit_config_regs │────▶│    pit_core      │  │
│  │   or         │     │                  │     │                  │  │
│  │ apb4_slave_cdc│     │  (PeakRDL Wrap)  │     │  (3 Counters)    │  │
│  │              │     │                  │     │                  │  │
│  └──────────────┘     └──────────────────┘     └──────────────────┘  │
│                                                                        │
│  APB Domain         │  Register Interface   │  Counter Domain         │
│  (pclk)             │                       │  (pit_clk or pclk)      │
└────────────────────────────────────────────────────────────────────────┘
         ▲                                              │
         │                                              ▼
    APB Interface                            GATE[2:0], OUT[2:0]
```

### Module Hierarchy

```
apb4_pit_8254
├── apb4_slave (CDC_ENABLE=0) or apb4_slave_cdc (CDC_ENABLE=1)
│   └── Converts APB protocol to cmd/rsp interface
├── pit_config_regs
│   ├── peakrdl_to_cmdrsp (protocol adapter)
│   └── pit_regs (PeakRDL generated)
│       └── Register file with hwif interface
└── pit_core
    ├── pit_counter (Counter 0)
    ├── pit_counter (Counter 1)
    └── pit_counter (Counter 2)
```

### Three-Layer Architecture

Following the HPET design pattern, the PIT uses a clean three-layer architecture:

**Layer 1: APB Interface (apb4_pit_8254)**
- Protocol conversion (APB → cmd/rsp)
- Optional clock domain crossing
- Top-level integration
- Parameter configuration

**Layer 2: Configuration Registers (pit_config_regs)**
- Register file integration
- Edge detection for write strobes
- Counter readback connection
- Status feedback aggregation

**Layer 3: Core Logic (pit_core + pit_counter)**
- Counter control and data routing
- Three independent pit_counter instances
- Mode 0 counting logic
- GATE/OUT signal management

## Functional Description

### Data Flow

**Write Path:**
```
APB Write → APB Slave → CMD Interface → PeakRDL Adapter →
→ PeakRDL Registers → hwif_out → Config Regs Wrapper →
→ PIT Core → Counter Instance → Counter Logic
```

**Read Path:**
```
Counter Value → count_reg_out → PIT Core → Config Regs →
→ hwif_in → PeakRDL Registers → Read Data → RSP Interface →
→ APB Slave → APB Read Data
```

### Counter Control State

There is no explicit state machine in `pit_counter`. Counter control is two
flags plus the count itself:

- **`r_null_count`** - set at reset, cleared by the first count load, and
  never set again. There is no path back to a "no count loaded" state short
  of a hardware reset.
- **`r_counting`** - set when a load occurs with `GATE=1` and the clock
  enabled (or when GATE/enable arrive after a load); cleared when the count
  reaches zero (terminal count, OUT goes high).

Behavior over a Mode 0 cycle:

1. Reset: `r_null_count=1`, `r_counting=0`, `OUT=0`.
2. Count load: count captured, `r_null_count` cleared, OUT driven low;
   counting starts immediately if `GATE=1` and the PIT is enabled, otherwise
   it starts when they next are (GATE is sampled here, not monitored during
   the count).
3. Counting: decrement on each enabled clock; GATE transitions are ignored.
4. Terminal count: at count 0, OUT goes high and `r_counting` clears. OUT
   stays high until the next load drives it low again.

### Control Flow

**Counter Programming Sequence:**
1. Write `PIT_CONTROL` with control word (counter select, mode, RW mode)
2. Control word decoded and routed to selected counter
3. Write `COUNTERx_DATA` with 16-bit count value
4. Counter loads value and starts counting (if GATE high and PIT enabled)
5. Counter decrements on each clock cycle
6. When count reaches 0, OUT goes high

**Status Readback:**
1. Read `PIT_STATUS` register
2. Returns 3 bytes (one per counter) with packed status fields
3. Status includes: OUT state, NULL_COUNT, RW mode, counter mode, BCD flag

## Timing

### Clock Domains

**Single Clock Mode (CDC_ENABLE=0):**
```
pclk ──┬──▶ APB Slave
       └──▶ Registers ──▶ Counters
```

**Dual Clock Mode (CDC_ENABLE=1):**
```
pclk ────▶ APB Slave ──▶ CDC ──┐
                                ├──▶ Registers
pit_clk ────────────────────────┴──▶ Counters
```

## Design Notes

### Reset Behavior

**Power-On Reset:**
- All counters: NULL_COUNT=1, counting=0, OUT=0
- PIT disabled (PIT_CONFIG=0)
- All count values cleared

**Soft Reset (PIT disable):**
- Counting pauses (the clock enable is gated; the internal counting flag is
  NOT cleared, so counting resumes where it left off on re-enable)
- Count values preserved
- OUT signals remain in current state
- NULL_COUNT flags unchanged

---

**Version:** 1.0
**Last Updated:** 2025-11-08
