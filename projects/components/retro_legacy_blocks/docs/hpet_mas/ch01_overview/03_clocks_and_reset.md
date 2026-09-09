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

# APB HPET Clocks and Reset

## Overview

The APB HPET operates in one or two clock domains depending on CDC configuration. Pick the mode that matches your system; the trade is latency versus clock freedom.

### Single Clock Domain (CDC_ENABLE = 0)

**Configuration:**
- `pclk = hpet_clk` (same physical clock)
- No clock domain crossing required
- Lower latency (2 APB clock cycles for register access)
- Simpler timing analysis

**Use Cases:**
- System where APB and timer clocks are guaranteed synchronous
- Resource-constrained designs (CDC overhead not needed)
- Minimal latency requirements

### Dual Clock Domains (CDC_ENABLE = 1)

**Configuration:**
- `pclk` and `hpet_clk` are independent, asynchronous clocks
- CDC synchronization required
- Higher latency (4-6 APB clock cycles for register access)
- More complex timing analysis

**Use Cases:**
- System where APB runs at different frequency than timer clock
- HPET clock derived from external crystal/oscillator
- Power management scenarios (clock gating one domain)

---

## Functional Description

### Clock Specifications

#### APB Clock (`pclk`)

**Purpose:** APB interface protocol clock

**Constraints:**
- Frequency: Typically 10-200 MHz (application-dependent)
- Duty cycle: 50% ±10%
- Jitter: < 5% of period
- No specific minimum/maximum frequency enforced in RTL

**Driven Blocks:**
- APB slave (or the pclk side of the APB CDC wrapper)
- PeakRDL register file and register configuration logic ONLY when
  CDC_ENABLE=0 (with CDC_ENABLE=1 they run on hpet_clk)

#### HPET Clock (`hpet_clk`)

**Purpose:** Timer counter increment and comparator evaluation

**Constraints:**
- Frequency: User-configurable (typically 1-100 MHz)
- Duty cycle: 50% ±10%
- Jitter: < 2% of period (affects timer accuracy)
- Must be stable and continuous when HPET enabled

**Driven Blocks:**
- Main counter increment
- Comparator match detection
- Timer control FSMs
- Interrupt generation logic

**Timer Accuracy:** Directly proportional to `hpet_clk` frequency and stability
- 10 MHz -> 100ns resolution
- 1 MHz -> 1µs resolution
- 1 kHz -> 1ms resolution

### Reset Domains

#### APB Reset (`presetn`)

**Type:** Asynchronous active-low reset

**Scope:** The APB front-end always; with `CDC_ENABLE=0` also the register
file and timer core (everything runs on `pclk` in that mode)

**Reset Behavior** (illustrative; with `CDC_ENABLE=1` the register file
resets from `hpet_clk`/`hpet_resetn` instead):
```systemverilog
always_ff @(posedge pclk or negedge presetn) begin
    if (!presetn) begin
        // Global configuration
        HPET_CONFIG <= 32'h0;         // HPET disabled
        HPET_STATUS <= 32'h0;         // mirror of the core's status (also reset there)

        // Per-timer configuration
        for (int i = 0; i < NUM_TIMERS; i++) begin
            TIMER_CONFIG[i] <= 32'h0;  // Timer disabled
        end
    end
end
```

**Reset Values:**
| Register | Reset Value | Description |
|----------|-------------|-------------|
| `HPET_CONFIG` | 32'h0 | Global disable, no legacy mapping |
| `HPET_STATUS` | 32'h0 | Mirror of the core's `r_interrupt_status`; both reset to 0 |
| `HPET_COUNTER_LO` | 32'h0 | Read/write; reads return the live counter |
| `HPET_COUNTER_HI` | 32'h0 | Read/write; reads return the live counter |
| `HPET_ID` | Constant | RO identification: vendor/revision are the low byte of `VENDOR_ID`/`REVISION_ID`, `num_tim_cap` = NUM_TIMERS-1, `leg_rt_cap` = 0 |
| `TIMER[i]_CONFIG` | 32'h0 | Timer disabled, one-shot mode |
| `TIMER[i]_COMPARATOR_LO` | 32'h0 | Read/write; reads return the last software-written value |
| `TIMER[i]_COMPARATOR_HI` | 32'h0 | Read/write; reads return the last software-written value |

#### HPET Reset (`hpet_resetn`)

**Type:** Asynchronous active-low reset

**Scope:** With `CDC_ENABLE=1`, the register file and timer core (both run on
`hpet_clk` in that mode). With `CDC_ENABLE=0` this reset is unused by the
core logic, which runs on `pclk`/`presetn`.

**Reset Behavior:**
```systemverilog
always_ff @(posedge hpet_clk or negedge hpet_resetn) begin
    if (!hpet_resetn) begin
        // Main counter
        r_main_counter <= 64'h0;

        // Per-timer state
        for (int i = 0; i < NUM_TIMERS; i++) begin
            r_timer_comparator[i] <= 64'h0;
            r_timer_period[i] <= 64'h0;
            r_timer_armed[i] <= 1'b1;
            r_comp_next_epoch[i] <= 1'b0;
            r_interrupt_status[i] <= 1'b0;
        end
    end
end
```

**Reset Values:**
| Signal | Reset Value | Description |
|--------|-------------|-------------|
| `r_main_counter` | 64'h0 | Counter starts at zero |
| `r_timer_comparator[i]` | 64'h0 | Comparators cleared |
| `r_timer_period[i]` | 64'h0 | Period storage cleared |
| `r_timer_armed[i]` | 1'b1 | Armed: counter == comparator == 0 is already a match, and the enables gate it until software is ready |
| `r_comp_next_epoch[i]` | 1'b0 | Next-epoch hold clear: the comparator is in the counter's current epoch, so the match is not held off |
| `r_interrupt_status[i]` | 1'b0 | Interrupt status cleared |

### Clock Domain Crossing Details

#### CDC Synchronization

When `CDC_ENABLE = 1`, the `apb4_slave_cdc` module handles all clock domain crossing:

**Write Path (pclk -> hpet_clk):**
```
1. APB write on pclk
2. Command written to APB-side holding registers
3. Command crosses to the hpet_clk domain through the async command FIFO
   (gaxi_fifo_async inside apb4_slave_cdc)
4. hpet_clk-side logic applies write to timer registers
5. Response crosses back through the async response FIFO
6. APB PREADY asserted (transaction complete)

Latency: 4-6 pclk cycles
```

**Read Path (hpet_clk -> pclk):**
```
1. APB read on pclk
2. Read request synchronized to hpet_clk
3. hpet_clk-side logic captures register data
4. Data synchronized back to pclk domain
5. APB PRDATA driven
6. APB PREADY asserted (transaction complete)

Latency: 4-6 pclk cycles
```

**Metastability Protection:**
- The crossing is a pair of async FIFOs (Gray/Johnson-coded pointers);
  only the FIFO pointers are synchronized -- data words never cross
  combinationally
- No toggle handshake exists; ordering and stability come from the FIFO

### Counter Read Atomicity

**Problem:** 64-bit counter spans two 32-bit APB registers

**Non-Atomic Read Sequence:**
```
1. Read HPET_COUNTER_LO -> captures lower 32 bits
2. Counter increments (may overflow from 0xFFFFFFFF to 0x00000000)
3. Read HPET_COUNTER_HI -> captures upper 32 bits (now incremented!)
4. Result: Lower 32 bits from time T, upper 32 bits from time T+1
```

**Software Workaround (Overflow Detection):**
```c
uint64_t read_hpet_counter(void) {
    uint32_t hi1, hi2, lo;

    do {
        hi1 = read_reg(HPET_COUNTER_HI);
        lo  = read_reg(HPET_COUNTER_LO);
        hi2 = read_reg(HPET_COUNTER_HI);
    } while (hi1 != hi2);  // Retry if overflow detected

    return ((uint64_t)hi2 << 32) | lo;
}
```

**Note:** Hardware atomic read not implemented (future enhancement)

### Clock Gating Considerations

**APB Clock Gating:**
- Safe to gate `pclk` when no APB transactions pending
- Must ensure APB master deasserts PSEL before gating
- Gating has no effect on HPET timer operation (hpet_clk independent)

**HPET Clock Gating:**
- **DO NOT gate `hpet_clk` while HPET enabled** (HPET_CONFIG[0] = 1)
- Counter will stop incrementing -> timers will not fire
- Safe to gate only when HPET_CONFIG[0] = 0 (disabled state)

**Power Saving Strategy:**
```
1. Disable HPET: Write HPET_CONFIG[0] = 0
2. Wait for any pending timer operations to complete
3. Gate hpet_clk
4. APB registers remain accessible (pclk still running)
5. To resume: Ungate hpet_clk, then write HPET_CONFIG[0] = 1
```

**Re-enabling does not re-fire expired timers.** The fire pulse is a raw
`counter >= comparator` match qualified by a per-timer armed latch that
clears when the timer fires and sets again only when the match falls
(or is held off by the next-epoch bit), when a comparator half is written
with the timer stopped, or when a periodic catch-up step lands at or
ahead of the counter. A one-shot that
completed before step 1 is still un-armed when step 5 runs, so the 0->1
of HPET_CONFIG[0] (or of a timer's own enable) while counter >= comparator
produces nothing. The one case that does fire on enable is the intended
one: a timer whose comparator was written while everything was disabled
-- even to a value the counter has already passed -- is armed, and fires
once as soon as both enables are on. A periodic timer left behind by a
counter write during the halt catches up silently at step 5: one fire at
the next boundary still ahead, the missed periods skipped rather than
burst. The silence has a length. A catch-up advances the comparator once
per cycle and closes the deficit by period - 1 counts each time (period
1 jumps to counter + 1 in one), so it costs cycles in proportion to the
deficit -- a period-2 timer left 2^52 counts behind catches up for
~2^52 cycles with no interrupt. That bound is a contract, not a defect,
and it is why the HPET specification and this book require the counter
halted (`HPET_CONFIG[0] = 0`) before it is written -- a torn or stale
half on a running counter is exactly how a 2^52 deficit appears -- and a
periodic comparator programmed near or ahead of the counter.

---

## Timing

### Reset Coordination

#### Synchronous Mode (CDC_ENABLE = 0)

**Requirement:** `presetn` and `hpet_resetn` should be asserted/deasserted together

**Recommended Connection:**
```systemverilog
assign hpet_resetn = presetn;  // Same reset for both domains
```

**Reset Sequence:**
```
1. Assert presetn = 0 (also asserts hpet_resetn = 0)
2. Hold for >= 10 clock cycles
3. Deassert presetn = 1 (also deasserts hpet_resetn = 1)
4. Wait >= 5 clock cycles before first register access
```

#### Asynchronous Mode (CDC_ENABLE = 1)

**Requirement:** Both resets can be independent but must overlap during power-on

**Recommended Sequence:**
```
1. Assert both presetn = 0 and hpet_resetn = 0
2. Hold presetn for >= 10 pclk cycles
3. Hold hpet_resetn for >= 10 hpet_clk cycles
4. Deassert resets (order not critical, but both must be stable)
5. Wait for CDC handshake to stabilize (>= 6 pclk cycles)
6. Begin register accesses
```

**Reset Timing Diagram (CDC Mode):**
```
           +-------------------------------------
presetn    +                                    (>=10 pclk cycles in reset)

                  +---------------------------------
hpet_resetn        +                              (>=10 hpet_clk cycles in reset)

                           +-------------------------
APB Access                 + Safe to access       (Wait for CDC stabilization)
```

### Timing Constraints

#### Setup/Hold Requirements

**APB Interface (Synchronous):**
```
Setup time:  2ns typical (technology-dependent)
Hold time:   1ns typical (technology-dependent)
```

**HPET Clock (Asynchronous with CDC):**
```
No setup/hold requirements between pclk and hpet_clk
CDC synchronizers handle all timing
```

#### Maximum Operating Frequencies

**Technology-Dependent Estimates (Post-Synthesis):**
- APB clock: 200+ MHz (typical modern process)
- HPET clock: 100+ MHz (limited by counter/comparator logic)
- Clock domain crossing: Synchronizers support arbitrary frequency ratios

**Recommended Operating Points:**
- APB clock: 10-100 MHz (typical SoC bus speeds)
- HPET clock: 1-50 MHz (sufficient for most timing applications)

---

## Navigation

**Next:** [Chapter 1.4 - Acronyms and Terminology](04_acronyms.md)
