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

### APB HPET - Clocks and Reset

#### Clock Domains

The APB HPET operates in one or two clock domains depending on CDC configuration:

##### Single Clock Domain (CDC_ENABLE = 0)

**Configuration:**
- `pclk = hpet_clk` (same physical clock)
- No clock domain crossing required
- Lower latency (2 APB clock cycles for register access)
- Simpler timing analysis

**Use Cases:**
- System where APB and timer clocks are guaranteed synchronous
- Resource-constrained designs (CDC overhead not needed)
- Minimal latency requirements

##### Dual Clock Domains (CDC_ENABLE = 1)

**Configuration:**
- `pclk` and `hpet_clk` are independent, asynchronous clocks
- CDC synchronization required
- Higher latency (4-6 APB clock cycles for register access)
- More complex timing analysis

**Use Cases:**
- System where APB runs at different frequency than timer clock
- HPET clock derived from external crystal/oscillator
- Power management scenarios (clock gating one domain)

#### Clock Specifications

##### APB Clock (`pclk`)

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

##### HPET Clock (`hpet_clk`)

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

#### Reset Domains

##### APB Reset (`presetn`)

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
        // HPET_STATUS: no reset in the generated RTL (defect, #46) --
        // readback undefined until first fire/clear; intended 0

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
| `HPET_STATUS` | undefined | Storage has no reset (RTL defect, #46); intended 32'h0 |
| `HPET_COUNTER_LO` | 32'h0 | Read/write; reads return the live counter |
| `HPET_COUNTER_HI` | 32'h0 | Read/write; reads return the live counter |
| `HPET_ID` | Constant | RO identification: vendor/revision fixed 0x01/0x01, `num_tim_cap` = NUM_TIMERS-1 |
| `TIMER[i]_CONFIG` | 32'h0 | Timer disabled, one-shot mode |
| `TIMER[i]_COMPARATOR_LO` | 32'h0 | Read/write; reads return the last software-written value |
| `TIMER[i]_COMPARATOR_HI` | 32'h0 | Read/write; reads return the last software-written value |

##### HPET Reset (`hpet_resetn`)

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
| `r_interrupt_status[i]` | 1'b0 | Interrupt status cleared |

#### Reset Coordination

##### Synchronous Mode (CDC_ENABLE = 0)

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

##### Asynchronous Mode (CDC_ENABLE = 1)

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

#### Clock Domain Crossing Details

##### CDC Synchronization

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

##### Counter Read Atomicity

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

#### Clock Gating Considerations

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

**Known RTL deviation (#46): re-enabling fires expired timers.** The fire
detector is an edge on (match && enables), so any 0->1 of HPET_CONFIG[0]
(or a timer's own enable) while counter >= comparator creates a fresh
match edge -- every completed one-shot re-fires the moment step 5 runs,
setting status and irq. After any re-enable, clear HPET_STATUS and/or
rewrite the comparators of expired timers before unmasking interrupts.

#### Timing Constraints

##### Setup/Hold Requirements

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

##### Maximum Operating Frequencies

**Technology-Dependent Estimates (Post-Synthesis):**
- APB clock: 200+ MHz (typical modern process)
- HPET clock: 100+ MHz (limited by counter/comparator logic)
- Clock domain crossing: Synchronizers support arbitrary frequency ratios

**Recommended Operating Points:**
- APB clock: 10-100 MHz (typical SoC bus speeds)
- HPET clock: 1-50 MHz (sufficient for most timing applications)

---

**Next:** [Chapter 1.4 - Acronyms and Terminology](04_acronyms.md)
