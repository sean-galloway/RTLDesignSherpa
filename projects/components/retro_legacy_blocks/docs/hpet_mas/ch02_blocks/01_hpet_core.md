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

### HPET Core - Timer Logic

#### Overview

The HPET core (`hpet_core.sv`) implements the fundamental timer functionality: a 64-bit free-running counter, per-timer comparators, and interrupt generation. This module operates entirely in the `hpet_clk` domain and contains all timing-critical logic.

**Block Diagram:**

### Figure 2.8: HPET Core Block Diagram

![HPET Core Block Diagram](../assets/svg/hpet_core.png)

HPET Core architecture showing main counter, timer comparators, match detection, and interrupt generation.

#### Key Features

- **64-bit Free-Running Counter**: Increments every HPET clock cycle, provides timestamp base
- **Configurable Timer Array**: 2, 3, or 8 independent timers (compile-time parameter)
- **64-bit Comparators**: Per-timer comparison values with full counter range
- **Dual Operating Modes**: One-shot and periodic modes per timer
- **Automatic Period Reload**: Periodic mode auto-increments comparator after each fire
- **Individual Interrupts**: Separate fire flag and interrupt output per timer
- **Counter Read/Write Access**: Software can read and write counter value via config registers

#### Interface Specification

##### Parameters

| Parameter | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `NUM_TIMERS` | int | 3 | 2, 3, 8 | Number of independent timers in array (the `apb4_hpet` top-level default is 2) |

##### Clock and Reset

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **clk** | logic | 1 | Input | Core clock (hpet_clk or pclk, selected by CDC_ENABLE at the top level) |
| **rst_n** | logic | 1 | Input | Active-low asynchronous reset |

##### Configuration Interface (from hpet_config_regs)

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **hpet_enable** | logic | 1 | Input | Global HPET enable (from HPET_CONFIG[0]) |
| **counter_write** | logic | 1 | Input | Write strobe for counter |
| **counter_wdata** | logic | 64 | Input | New counter value (from HPET_COUNTER_LO/HI) |
| **timer_enable[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Input | Per-timer enable (from TIMER_CONFIG[2]) |
| **timer_int_enable[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Input | Per-timer interrupt enable (from TIMER_CONFIG[3]) |
| **timer_type[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Input | Per-timer mode: 0=One-shot, 1=Periodic (from TIMER_CONFIG[4]) |
| **timer_size[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Input | Per-timer compare width: 0=32-bit, 1=64-bit (from TIMER_CONFIG[5]) |
| **timer_comp_write[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Input | Per-timer comparator write strobe |
| **timer_comp_wdata[NUM_TIMERS]** | logic [63:0] | NUM_TIMERS x 64 | Input | Per-timer comparator write data |
| **timer_comp_write_high** | logic | 1 | Input | Selects which 32-bit half a comparator write updates |

##### Status Interface (to hpet_config_regs)

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **counter_rdata** | logic | 64 | Output | Current main counter value (to HPET_COUNTER_LO/HI) |
| **timer_comp_rdata[NUM_TIMERS]** | logic [63:0] | NUM_TIMERS x 64 | Output | Live comparator values (currently unconsumed by the wrapper) |
| **timer_int_status[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Output | Per-timer sticky interrupt status (to HPET_STATUS) |
| **timer_int_clear[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Input | Status clear strobes from the register wrapper (W1C) |

##### Interrupt Interface

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **timer_irq[NUM_TIMERS-1:0]** | logic | NUM_TIMERS | Output | Per-timer interrupt outputs (active-high) |

#### Per-Timer State Machine

Each timer instance implements an identical FSM controlling its operation:

### Figure 2.9: Timer FSM

![Timer FSM](../assets/svg/hpet_core_fsm.png)

##### FSM States

| State | Encoding | Description |
|-------|----------|-------------|
| **IDLE** | Default | Timer disabled, waiting for enable signal |
| **ARMED** | Active | Timer enabled, monitoring counter vs comparator |
| **FIRE** | Transient | Timer match detected, asserting interrupt (1 cycle) |
| **PERIODIC_RELOAD** | Transient | Periodic mode: auto-increment comparator (1 cycle) |
| **ONE_SHOT_COMPLETE** | Sticky | One-shot mode: timer complete, waiting for reconfigure |

**Note:** FSM is **conceptual** - implementation uses combinational logic rather than explicit state registers for simplicity and timing.

##### State Transitions

**IDLE -> ARMED:**
- Condition: `hpet_enable && timer_enable[i]`
- Action: Latch current comparator value
- Duration: Immediate (next clock cycle)

**ARMED -> FIRE:**
- Condition: `counter_value >= timer_comparator[i]`
- Action: Assert `timer_int_status[i]` (sticky)
- Duration: 1 clock cycle (fire is edge-detected)

**FIRE -> PERIODIC_RELOAD:**
- Condition: `timer_type[i] == 1` (periodic mode)
- Action: `timer_comparator[i] <= timer_comparator[i] + timer_period[i]`
- Duration: 1 clock cycle

**FIRE -> ONE_SHOT_COMPLETE:**
- Condition: `timer_type[i] == 0` (one-shot mode)
- Action: Hold `timer_int_status[i]` until software clears
- Duration: Until STATUS cleared or timer disabled

**PERIODIC_RELOAD -> ARMED:**
- Condition: Always (automatic)
- Action: Resume monitoring with new comparator value
- Duration: Immediate

**ONE_SHOT_COMPLETE -> ARMED:**
- Condition: Comparator updated while timer remains enabled
- Action: Resume monitoring with new comparator value
- Duration: Immediate on comparator write strobe
- Caveat: fire detection is edge-based (`w_timer_fire = match & ~match_prev`),
  so the new comparator must exceed the current counter value. Writing a
  comparator at or below the counter produces no new match edge and the
  timer never re-fires.

**ARMED/ONE_SHOT_COMPLETE -> IDLE:**
- Condition: `!hpet_enable || !timer_enable[i]`
- Action: Stop match generation. A pending interrupt status/output is NOT
  cleared by disabling -- it holds until software W1C or reset.
- Duration: Immediate

#### Main Counter Logic

##### Counter Increment

```systemverilog
// 64-bit free-running counter
logic [63:0] r_main_counter;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_main_counter <= 64'h0;
    end else if (counter_write) begin
        // Software write to counter
        r_main_counter <= counter_wdata;
    end else if (hpet_enable) begin
        // Continuous increment when HPET enabled
        r_main_counter <= r_main_counter + 64'h1;
    end
    // else: Hold value when HPET disabled
end

// Output current counter value
assign counter_rdata = r_main_counter;
```

**Key Behavior:**
- **Reset**: Counter initializes to 0
- **Software Write**: Counter can be written via HPET_COUNTER_LO/HI registers
- **Increment**: Counter increments every clock when `hpet_enable = 1`
- **Overflow**: Counter wraps from 64'hFFFF_FFFF_FFFF_FFFF to 64'h0 naturally

##### Counter Timing

```
Clock:      --+ +-+ +-+ +-+ +-+ +-
hpet_clk      +-+ +-+ +-+ +-+ +-

Enable:     --------+
hpet_enable         +-------------

Counter:    [N] [N] [N+1][N+2][N+3]
r_main_counter

Latency: 1 cycle from enable to first increment
```

#### Timer Comparator Logic

##### Comparator Storage (Per-Timer)

```systemverilog
// Per-timer comparator and period storage
logic [63:0] r_timer_comparator [NUM_TIMERS-1:0];
logic [63:0] r_timer_period [NUM_TIMERS-1:0];

for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_timer_comparators
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_timer_comparator[i] <= 64'h0;
            r_timer_period[i] <= 64'h0;
        end else if (timer_comp_write[i]) begin
            // Software write updates ONE 32-bit half per write, selected
            // by timer_comp_write_high (after a periodic auto-advance, a
            // lone LO write yields {auto-advanced HI, new LO})
            if (timer_comp_write_high) begin  // 1-bit port: |timer_comp_hi_write
                r_timer_comparator[i][63:32] <= timer_comp_wdata[i][63:32];
                r_timer_period[i][63:32]     <= timer_comp_wdata[i][63:32];
            end else begin
                r_timer_comparator[i][31:0] <= timer_comp_wdata[i][31:0];
                r_timer_period[i][31:0]     <= timer_comp_wdata[i][31:0];
            end
        end else if (w_timer_fire[i] && timer_type[i]) begin
            // Periodic mode auto-reload
            r_timer_comparator[i] <= r_timer_comparator[i] + r_timer_period[i];
        end
        // else: Hold value
    end
end
```

**Key Behavior:**
- **Reset**: Comparator and period clear to 0
- **Initial Write**: Both comparator and period latched from same write
- **Periodic Mode**: Comparator auto-increments by period value on each fire
- **One-Shot Mode**: Comparator remains constant after initial write

##### Match Detection

**64-bit Comparator Match Waveform:**

### Waveform 2.10: Comparator Match Behavior

![Comparator Match Behavior](../assets/waves/comparator_match.json)

*Use [WaveDrom Editor](https://wavedrom.com/editor.html) to view/edit, or generate SVG with `wavedrom-cli`*

```systemverilog
// Per-timer match detection (combinational)
logic [NUM_TIMERS-1:0] w_timer_match;

for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_timer_match
    // timer_size (TIMER_CONFIG[5]) selects 64-bit or 32-bit compare
    assign w_timer_match[i] = (timer_size[i]
                               ? (r_main_counter >= r_timer_comparator[i])
                               : (r_main_counter[31:0] >= r_timer_comparator[i][31:0])) &&
                              timer_enable[i] &&
                              hpet_enable;
end
```

**Match Conditions:**
- Counter value >= comparator value (full 64 bits when timer_size=1,
  low 32 bits only when timer_size=0)
- Timer individually enabled (`timer_enable[i] = 1`)
- HPET globally enabled (`hpet_enable = 1`)

#### Timer Fire Logic

##### Fire Detection (Rising Edge)

```systemverilog
// Per-timer previous match state for edge detection
logic [NUM_TIMERS-1:0] r_timer_match_prev;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_timer_match_prev <= '0;
    end else begin
        r_timer_match_prev <= w_timer_match;
    end
end

// Rising edge detection: fire on transition from no-match to match
logic [NUM_TIMERS-1:0] w_timer_fire_edge;

for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_timer_fire_edge
    assign w_timer_fire_edge[i] = w_timer_match[i] && !r_timer_match_prev[i];
end
```

**Fire Edge Timing:**
```
Clock:      --+ +-+ +-+ +-+ +-+ +-
hpet_clk      +-+ +-+ +-+ +-+ +-

Counter:    [99][100][101][102][103]
r_main_counter

Comparator:      [100]
                (constant)

Match:      ------+
w_timer_match     +-----------

Match Prev: --------+
r_timer_match_prev  +---------

Fire Edge:  ----+ +-
w_timer_fire_edge +-

Fired Flag: ----+
timer_int_status[i]  +--------

Note: Fire edge is 1-cycle pulse on rising edge of match
```

##### Fire Flag Management

```systemverilog
// Per-timer sticky interrupt status -- identical in BOTH modes
logic [NUM_TIMERS-1:0] r_interrupt_status;

for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_interrupt_logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_interrupt_status[i] <= 1'b0;
        end else if (timer_int_clear[i]) begin
            r_interrupt_status[i] <= 1'b0;   // Software W1C
        end else if (w_timer_fire[i]) begin
            r_interrupt_status[i] <= 1'b1;   // Set on fire edge
        end
    end
end

// Sticky status to the register wrapper (drives HPET_STATUS)
assign timer_int_status = r_interrupt_status;
```

**Fire Flag Behavior:**
- **Both modes are sticky**: the status bit sets on the fire edge and holds
  until software clears it via HPET_STATUS W1C (or reset). There is no
  `timer_type` term in the interrupt logic -- periodic mode does NOT pulse
  the status per period; from the first fire it stays asserted until W1C,
  while the comparator keeps auto-advancing in the background.

#### Interrupt Generation

**Interrupt Generation and Acknowledgment Waveform:**

### Waveform 2.11: Interrupt Generation

![Interrupt Generation](../assets/waves/interrupt_generation.json)

*Use [WaveDrom Editor](https://wavedrom.com/editor.html) to view/edit, or generate SVG with `wavedrom-cli`*

##### Interrupt Output Logic

```systemverilog
// Per-timer interrupt output -- a flop, gated by int_enable AT FIRE TIME
for (genvar i = 0; i < NUM_TIMERS; i++) begin : gen_interrupt_output
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_interrupt_output[i] <= 1'b0;
        end else if (timer_int_clear[i]) begin
            r_interrupt_output[i] <= 1'b0;
        end else if (w_timer_fire[i] && timer_int_enable[i]) begin
            r_interrupt_output[i] <= 1'b1;
        end else if (!r_interrupt_status[i]) begin
            r_interrupt_output[i] <= 1'b0;   // Follows status clear
        end
    end
end

assign timer_irq = r_interrupt_output;
```

**Interrupt Behavior:**
- **Registered**: `timer_irq` asserts one core clock after the fire event
- **Gated at fire time**: `timer_int_enable[i]` is sampled only when the
  fire edge occurs. Enabling interrupts AFTER a timer has fired does not
  retroactively assert `timer_irq`, even though the status bit is set.
- **Sticky in both modes**: asserted from (fire + 1 cycle) until the W1C

**Interrupt Clearing:**
Software clears interrupts by writing 1 to the corresponding HPET_STATUS bit
(W1C). The sticky status lives in `hpet_core` (`r_interrupt_status`) and is
mirrored into the PeakRDL HPET_STATUS register by the wrapper. Note the known
RTL deviation tracked in issue #46: the wrapper's clear strobe fires on ANY
HPET_STATUS write, clearing every pending core status bit rather than only
the bits written with 1.

#### Periodic Mode Details

**Periodic Timer Waveform:**

### Waveform 2.12: Periodic Timer Operation

![Periodic Timer Operation](../assets/waves/periodic_timer.json)

*Use [WaveDrom Editor](https://wavedrom.com/editor.html) to view/edit, or generate SVG with `wavedrom-cli`*

##### Period Storage and Auto-Reload

**Initial Comparator Write:**
```
Software writes: TIMER0_COMPARATOR = 1000
Result:
  r_timer_comparator[0] = 1000
  r_timer_period[0] = 1000  (also latched)
```

**First Fire (at counter = 1000):**
```
Fire edge detected
-> timer_int_status[0] asserts
-> Comparator auto-reloads:
  r_timer_comparator[0] = 1000 + 1000 = 2000
```

**Second Fire (at counter = 2000):**
```
Fire edge detected
-> timer_int_status[0] asserts
-> Comparator auto-reloads:
  r_timer_comparator[0] = 2000 + 1000 = 3000
```

**Process repeats indefinitely until timer disabled**

##### Periodic Mode Timing Example

```
Clock Cycles:   0   1000 1001 2000 2001 3000 3001 ...

Counter:        0 -> 1000 1001 2000 2001 3000 3001 ...

Comparator:     [1000] [2000] [3000] [4000] ...
                   ↑      ↑      ↑
                Fire 1  Fire 2  Fire 3

timer_int_status: --+
                    +---------------... (sticky: set at Fire 1, holds
                                         through Fire 2/3 until SW W1C)

timer_irq:        --+
                    +---------------... (same shape, one cycle later)

Period = 1000 HPET clock cycles (constant). The comparator keeps advancing
each period, but status/irq do NOT pulse per fire -- they stay asserted from
the first fire until software clears HPET_STATUS.
```

#### One-Shot Mode Details

**One-Shot Timer Waveform:**

### Waveform 2.13: One-Shot Mode Operation

![One-Shot Mode Operation](../assets/waves/oneshot_mode.json)

*Use [WaveDrom Editor](https://wavedrom.com/editor.html) to view/edit, or generate SVG with `wavedrom-cli`*

##### Fire-Once Behavior

**Initial Comparator Write:**
```
Software writes: TIMER0_COMPARATOR = 5000
Result:
  r_timer_comparator[0] = 5000
  (period not used in one-shot mode)
```

**Fire Event (at counter = 5000):**
```
Fire edge detected
-> timer_int_status[0] asserts (sticky)
-> Comparator remains at 5000 (no auto-reload)
-> Interrupt remains asserted
```

**Interrupt Clearing:**
```
Software writes: HPET_STATUS[0] = 1 (W1C)
Result:
  timer_int_status[0] clears
  timer_irq[0] clears
```

**Reconfiguration:**
```
Software writes: TIMER0_COMPARATOR = 10000
Result:
  r_timer_comparator[0] = 10000
  Timer re-arms, waits for counter = 10000
```

##### One-Shot Mode Timing Example

```
Clock Cycles:   0   5000 5001 5002 ...

Counter:        0 -> 5000 5001 5002 ...

Comparator:     [5000] [5000] [5000] ...
                   ↑
                Fire (once)

timer_int_status: --+
                    +-------------... (sticky until SW clear)

timer_irq:        --+
                    +-------------... (one cycle later, follows status)

Software Write: ------+ +-
HPET_STATUS[0]=1      +-

timer_int_status: --+     +-
(after clear)       +-----+

Fire only once, interrupt sticky until software clear
```

#### Resource Utilization

**Per-Timer Resources (Estimated):**
- 64-bit comparator register: 64 flip-flops
- 64-bit period register: 64 flip-flops
- Match comparator: 64-bit >= comparison (~80 LUTs)
- Fire edge detection: 2 flip-flops + XOR gate
- Total per timer: ~128 flip-flops, ~85 LUTs

**Shared Resources:**
- 64-bit main counter: 64 flip-flops + 64-bit adder (~70 LUTs)
- Global enable logic: ~10 LUTs

**Total (NUM_TIMERS = 3):**
- Flip-flops: 64 + (128 × 3) = 448 FF
- LUTs: 80 + (85 × 3) = 335 LUTs

---

**Next:** [Chapter 2.2 - hpet_config_regs](02_hpet_config_regs.md)
